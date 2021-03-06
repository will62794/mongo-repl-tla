----------------------------- MODULE MongoRepl -----------------------------
(**************************************************************************************************)
(* A high level specification of the MongoDB replication protocol, which is based on a modified   *)
(* version of the Raft consensus protocol.                                                        *)
(*                                                                                                *)
(* This specification allows for the definition of precise correctness properties, which can be   *)
(* found in their own section.                                                                    *)
(**************************************************************************************************)

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC, Properties

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Secondary, Candidate, Primary

\* A reserved value.
CONSTANTS Nil

\* Optionally disable/enable these protocols by setting these constants to TRUE or FALSE.
CONSTANT EnableLearnerProtocol, EnableRollbackProtocol

(**************************************************************************************************)
(* Global variables                                                                               *)
(**************************************************************************************************)

VARIABLE messages

\* A history variable used in the proof. This would not be present in an
\* implementation. Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
VARIABLE elections

\* A history variable used in the proof. This would not be present in an
\* implementation. Keeps track of every log ever in the system (set of logs).
VARIABLE allLogs

\* Set of all immediately committed <<index, term>> log entry pairs.
VARIABLE immediatelyCommitted

(**************************************************************************************************)
(* Per server variables.                                                                          *)
(*                                                                                                *)
(* These are all functions with domain Server.                                                    *)
(**************************************************************************************************)

\* The server's term number.
VARIABLE currentTerm

\* The server's state (Secondary, Candidate, or Primary).
VARIABLE state

\* The candidate the server voted for in its current term, or  Nil if it hasn't voted for any.
VARIABLE votedFor

\* A function maintained on each server that contains a local view of how far each node think
\* every other node has applied to in its log. Maps from server id to <<index, term>> tuple.
VARIABLE matchEntry

serverVars == <<currentTerm, state, votedFor>>

\* A sequence of log entries. The index into this sequence is the index of the log entry.
VARIABLE log

\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:

\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded

\* The set of servers from which the candidate has received a vote in its currentTerm.
VARIABLE votesGranted

\* A history variable that would not be present in an implementation. 
\* It is a function from each server that voted for this candidate 
\* in its currentTerm to that voter's log.
VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted, voterLog>>

leaderVars == <<elections>>

\* all non-history variables:
\* <<messages,currentTerm,elections,matchEntry,state,votedFor,log,commitIndex,votesResponded,votesGranted,voterLog>>
varsNonHistory == <<candidateVars, serverVars, leaderVars, logVars, matchEntry, messages>>
vars == <<allLogs, immediatelyCommitted, varsNonHistory>>

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Generic helper operators                                                                       *)
(**************************************************************************************************)

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}
    
\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Return the range of a given function.
Range(f) == {f[x] : x \in DOMAIN f}

\* Is a sequence empty.
Empty(s) == Len(s) = 0

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Next state actions.                                                                            *)
(*                                                                                                *)
(* This section defines the core steps of the algorithm, along with some related helper           *)
(* definitions/operators.  We annotate the main actions with an (ACTION) specifier to disinguish  *)
(* them from auxiliary, helper operators.                                                         *)
(**************************************************************************************************)    

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Can node 'i' currently cast a vote for a node based on a received vote request.
CanVoteFor(i, voteRequest) == 
    LET logOk == 
        \/ voteRequest.mlastLogTerm > LastTerm(log[i])
        \/ /\ voteRequest.mlastLogTerm = LastTerm(log[i])
           /\ voteRequest.mlastLogIndex >= Len(log[i]) IN
    /\ voteRequest.mterm >= currentTerm[i]
    /\ votedFor[i] = Nil
    /\ logOk

\* Is it possible for log 'lj' to roll back based on the log 'li'. If this is true, it implies that
\* log 'lj' should remove entries to become a prefix of 'li'.
CanRollback(li, lj) == 
    /\ Len(li) > 0 
    /\ Len(lj) > 0
    \* The terms of the last entries of each log do not match. The term of node i's last 
    \* log entry is greater than that of node j's.
    /\ li[Len(li)].term > lj[Len(lj)].term

\* Returns the highest common index between two divergent logs, 'li' and 'lj'. 
\* If there is no common index between the logs, returns 0.
RollbackCommonPoint(li, lj) == 
    LET commonIndices == {k \in DOMAIN li : 
                            /\ k <= Len(lj)
                            /\ li[k] = lj[k]} IN
        IF commonIndices = {} THEN 0 ELSE Max(commonIndices)

QuorumAgreeInSameTerm(matchEntryVal) == 
    LET quorums == {Q \in Quorum :
                    \* Make sure all nodes in quorum have actually applied some entries.
                    /\ \A s \in Q : matchEntryVal[s][1] > 0
                    \* Make sure every applied entry in quorum has the same term.
                    /\ \A s, t \in Q : 
                       s # t => matchEntryVal[s][2] = matchEntryVal[t][2]} IN
        IF quorums = {} THEN Nil ELSE CHOOSE x \in quorums : TRUE    
       
(**************************************************************************************************)
(* Node 'i' sends out log entries.  (ACTION)                                                      *)
(*                                                                                                *)
(* Includes its entire log, for simplicity.  This message can be received by any other node.      *)
(* This would likely be implemented as a node first sending out a GetEntries request and a node   *)
(* receiving it and responding with logs.  We abstract this a bit by saying that nodes can send   *)
(* out log entries at any time, to any node.                                                      *)
(*                                                                                                *)
(* This models a generalized form of log transferral between nodes.  Any node can send log        *)
(* entries to any other node.  We reduce "pull-based" log retrieval to just the arbitrary sending *)
(* of log entries.  That is, a request for new entries sent from node i to node j is simply       *)
(* modeled as node j spontaneously sending out new log entries.  Any node can then receive these  *)
(* log entries and append them if they pass the consistency check i.e.  if their log is a prefix  *)
(* of the sender's log at the time the entries were sent.                                         *)
(*                                                                                                *)
(* In MongoDB, this action is implemented by secondary nodes: they select another node to sync    *)
(* from (their "sync source") and then fetch new entries by opening a cursor on their source's    *)
(* oplog.  Upon retrieval of the first batch from this oplog cursor they will perform the log     *)
(* consistency check.  After that point they are guaranteed to receive contiguous sections of     *)
(* their sync source's oplog, until the cursor dies or they choose to switch their sync source    *)
(* for whatever reason.                                                                           *)
(**************************************************************************************************)
SendEntries(i) == 
    /\ Len(log[i]) > 0
    /\ LET m == [type    |-> "SendEntries", 
                 fullLog |-> log[i], 
                 mterm   |-> currentTerm[i],
                 mcommitIndex |-> commitIndex[i]] IN
       messages' = messages \cup {m}
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, matchEntry>>

(**************************************************************************************************)
(* Node i processes a SendEntries message.  (ACTION)                                              *)
(*                                                                                                *)
(* This appends a new entry from the log in the message if the consistency check passes.          *)
(**************************************************************************************************)
HandleSendEntries(i) == 
    \E m \in messages : 
        /\ state[i] = Secondary
        /\ m.type = "SendEntries"
        /\ Len(m.fullLog) > Len(log[i])
        \* Log consistency check.
        /\ IF Len(log[i]) = 0 THEN TRUE
           ELSE LastTerm(log[i]) = m.fullLog[Len(log[i])].term
        \* Append one new entry. 
        /\ LET newEntry == m.fullLog[Len(log[i]) + 1] IN
           log' = [log EXCEPT ![i] = Append(log[i], newEntry)]
        \* Update term if needed.
        /\ currentTerm' = [currentTerm EXCEPT ![i] = Max({currentTerm[i], m.mterm})]
        \* Update commitIndex if newer.
        /\ commitIndex' = 
                [commitIndex EXCEPT ![i] = 
                    IF m.mcommitIndex[1] > commitIndex[i][1] THEN m.mcommitIndex ELSE commitIndex[i]]
        /\ messages' = messages \ {m}
        /\ UNCHANGED <<state, votedFor, candidateVars, leaderVars, matchEntry>>
    
(**************************************************************************************************)
(* Node 'i' becomes a primary.  (ACTION)                                                          *)
(**************************************************************************************************)     
BecomePrimary(i) == 
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Primary]
    /\ matchEntry' = [matchEntry EXCEPT ![i] = [j \in Server |-> <<0, 0>>]]
    /\ elections'  = elections \cup
                         {[eterm     |-> currentTerm[i],
                           eleader   |-> i,
                           elog      |-> log[i],
                           evotes    |-> votesGranted[i],
                           evoterLog |-> voterLog[i]]}        
    /\ UNCHANGED <<messages,currentTerm,votedFor,log,commitIndex,votesResponded,votesGranted,voterLog>>

(**************************************************************************************************)
(* Node 'i' times out and starts a new election.  (ACTION)                                        *)
(**************************************************************************************************)
Timeout(i) == 
    /\ state[i] \in {Secondary, Candidate}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    \* Vote for yourself immediately.
    /\ votedFor' = [votedFor EXCEPT ![i] = i] 
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {i}]
    /\ voterLog'       = [voterLog EXCEPT ![i] =  (i :> log[i])]  
    /\ UNCHANGED <<messages,elections,matchEntry,log,commitIndex>>

(**************************************************************************************************)
(* Candidate node 'i' sends out RequestVote requests.  (ACTION)                                   *)
(*                                                                                                *)
(* We send out messages to potential voters all at once, to simplify the model.                   *)
(**************************************************************************************************)
RequestVotes(i) ==
    /\ state[i] = Candidate
    /\ LET msgs == [type          : {"RequestVoteRequest"},
                    mterm         : {currentTerm[i]},
                    mlastLogTerm  : {LastTerm(log[i])},
                    mlastLogIndex : {Len(log[i])},
                    msource       : {i},
                    mdest         : (Server \ votesResponded[i])] IN
       messages' = messages \cup msgs
    /\ UNCHANGED <<currentTerm,elections,matchEntry,state,votedFor,log,commitIndex,votesResponded,votesGranted,voterLog>>

(**************************************************************************************************)
(* Node 'i' receives a RequestVote request from server 'j'.  (ACTION)                             *)
(**************************************************************************************************)
HandleRequestVoteRequest(i, j) == 
    \E m \in messages:
        /\ m.type = "RequestVoteRequest"
        /\ m.mdest = i
        /\ m.msource = j
        /\ CanVoteFor(i, m)
        /\ votedFor' = [votedFor EXCEPT ![i] = j]
        \* Update term.
        /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm] 
        /\ LET res == [type        |-> "RequestVoteResponse",
                       mterm        |-> m.mterm,
                       mvoteGranted |-> TRUE,
                       \* mlog is used just for the `elections' history variable for
                       \* the proof. It would not exist in a real implementation.
                       mlog         |-> log[i],
                       msource      |-> i,
                       mdest        |-> j] IN
         /\ messages' = (messages \cup {res}) \ {m}
         /\ UNCHANGED <<elections,matchEntry,state,log,commitIndex,votesResponded,votesGranted,voterLog>>

(**************************************************************************************************)
(* Node 'i' receives a RequestVote response from node 'j' (ACTION)                                *)
(**************************************************************************************************)
HandleRequestVoteResponse(i, j) == 
    \E m \in messages:
        /\ m.type = "RequestVoteResponse"
        /\ m.mdest = i
        /\ m.msource = j
        /\ m.mterm  = currentTerm[i]
        /\ m.mvoteGranted
        /\ votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \cup {j}]
        /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {j}]
        /\ voterLog' = [voterLog EXCEPT ![i] = voterLog[i] @@ (j :> m.mlog)]
        /\ messages' = messages \ {m}
        /\ UNCHANGED <<currentTerm,elections,matchEntry,state,votedFor,log,commitIndex>>
      
(**************************************************************************************************)
(* Node 'i', a primary, handles a new client request and places the entry in its log.  (ACTION)   *)
(**************************************************************************************************)        
ClientRequest(i, v) == 
    /\ state[i] = Primary
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> v]
       newLog == Append(log[i], entry) IN
       /\ log' = [log EXCEPT ![i] = newLog]
       /\ matchEntry' = [matchEntry EXCEPT ![i][i] = <<Len(newLog), entry.term>>]
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, commitIndex, messages>>
 
(**************************************************************************************************)
(* Node 'j' removes entries based against the log of node 'i'.  (ACTION)                          *)
(*                                                                                                *)
(* The rollback procedure used in this protocol is always executed by comparing the logs of two   *)
(* separate nodes.  By doing so, it is possible to determine if one node has a "divergent" log    *)
(* suffix, and thus has entries in its log that are uncommitted.  The essential idea is to see if *)
(* the last term of the entry of one log is less than the last term of the last entry of another  *)
(* log.  In this case, the log with the lesser last term should be considered eligible for        *)
(* rollback.  Note that the goal of this rollback procedure should be to truncate entries from a  *)
(* log that are both uncommitted, and also only truncate entries that it knows will NEVER become  *)
(* committed.  Of course, log entries that are written down by a primary before being replicated  *)
(* are clearly uncommitted, but deleting them wouldn't be sensible, since it is very possible     *)
(* those entries WILL become committed in the future.                                             *)
(**************************************************************************************************)
RollbackEntries(i, j) == 
    /\ state[j] = Secondary \* Primaries can only append to their logs.
    /\ CanRollback(log[i], log[j])
    /\ LET commonPoint == RollbackCommonPoint(log[i], log[j]) IN
           \* If there is no common entry between log 'i' and
           \* log 'j', then it means that the all entries of log 'j'
           \* are divergent, and so we erase its entire log. Otherwise
           \* we erase all log entries after the newest common entry. Note that 
           \* if the commonPoint is '0' then SubSeq(log[i], 1, 0) will evaluate
           \* to <<>>, the empty sequence.
           log' = [log EXCEPT ![j] = SubSeq(log[i], 1, commonPoint)] 
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, commitIndex, matchEntry, messages>>

(**************************************************************************************************)
(* Node 'i' updates node 'j' with its latest log application progress.  (ACTION)                  *)
(*                                                                                                *)
(* This is modeled as a single atomic step.                                                       *)
(**************************************************************************************************)
UpdatePosition(i, j) == 
    /\ Len(log[i]) > 0
    \* If node 'j' gives a progress update to node 'i', it must make sure to
    \* update the term of node 'i' with its own term, if it is higher. In a real system,
    \* this action would occur by 'j' sending a progress update message to 'i' that includes 
    \* the term of 'j' at the time of sending. Upon receiving the message, 'i' would update its
    \* own term if it was smaller than the term attached to the message.
    /\ currentTerm' = [currentTerm EXCEPT ![j] = Max({currentTerm[i], currentTerm[j]})]
    \* Primary nodes must revert to Secondary state if they increment their local term.
    /\ state' = [state EXCEPT ![j] = IF currentTerm[i] > currentTerm[j] THEN Secondary ELSE @]
    /\ LET lastEntry == <<Len(log[i]), LastTerm(log[i])>> IN
           /\ matchEntry' = [matchEntry EXCEPT ![j][i] = lastEntry] 
    /\ UNCHANGED <<votedFor, candidateVars, logVars, leaderVars, commitIndex, messages>>        

(**************************************************************************************************)
(* Advances the commit point on server 'i'.  (ACTION)                                             *)
(*                                                                                                *)
(* The commit point is calculated based on node i's current 'matchEntry' vector.  Choose the      *)
(* highest index that is agreed upon by a majority.  We are only allowed to choose a quorum whose *)
(* last applied entries have the same term.                                                       *)
(*                                                                                                *)
(* Only allow primaries to advance the commit point for now.  In general, we should be able to    *)
(* extend this rule so that secondaries can also advance commit point by similar means.           *)
(**************************************************************************************************)
AdvanceCommitPoint(i) == 
    LET quorumAgree == QuorumAgreeInSameTerm(matchEntry[i]) IN
        /\ state[i] = Primary
        /\ quorumAgree # Nil
        \* The term of the entries in the quorum must match our current term.
        /\ LET serverInQuorum == CHOOSE s \in quorumAgree : TRUE
               termOfQuorum == matchEntry[i][serverInQuorum][2] 
               \* The minimum index of the applied entries in the quorum.
               newCommitIndex == Min({matchEntry[i][s][1] : s \in quorumAgree}) IN
               /\ termOfQuorum = currentTerm[i]
               \* We store the commit index as an <<index, term>> pair instead of just an
               \* index, so that we can uniquely identify a committed log prefix.
               /\ commitIndex' = [commitIndex EXCEPT ![i] = <<newCommitIndex, termOfQuorum>>]
        /\ UNCHANGED << serverVars, candidateVars, leaderVars, log, matchEntry, messages>>  

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(*                                                                                                *)
(* Correctness Properties                                                                         *)
(*                                                                                                *)
(**************************************************************************************************)

\* The set of all log entries in a given log i.e. the set of all <<index, term>>
\* pairs that appear in the log.
LogEntries(xlog) == {<<i, xlog[i].term>> : i \in DOMAIN xlog}

\* Is <<index, term>> in the given log.
EntryInLog(xlog, index, term) == <<index, term>> \in LogEntries(xlog)

\* The set of all log entries (<<index, term>>) that appear in any log in the given log set.
AllLogEntries(logSet) == UNION {LogEntries(l) : l \in logSet}      

\* Determines whether an <<index, term>> entry is immediately committed, based on the
\* current state. Be careful to note that the value of this expression only depends on the current state, not the 
\* history of states. A particular entry may be immediately committed in the current state,
\* but not immediately committed in the next state.
ImmediatelyCommitted(index, term) == 
    \E Q \in Quorum :
        \A q \in Q : 
\*            /\ currentTerm[q] <= term 
            /\ currentTerm[q] = term 
            /\ EntryInLog(log[q], index, term)

\* The set of all immediately committed log entries in the current state. An entry is committed
\* at a particular term t, so we store the entry itself along with the term at which it was committed. 
\* In general, the "commitment term" doesn't need to match the term of the entry itself, although for 
\* immediately committed entries, it will. It may not for prefix committed entries, though.
AllImmediatelyCommitted == 
    LET entries == {e \in AllLogEntries(Range(log)) : ImmediatelyCommitted(e[1], e[2])} IN
    {[entry |-> e, term |-> e[2]] : e \in entries}

\* The set of prefix committed entries.
PrefixCommittedEntries == 
    {e \in AllLogEntries(Range(log)) :
        \E l \in Range(log) : 
            /\ EntryInLog(l, e[1], e[2])
            /\ \E c \in LogEntries(l) :
                /\ c[1] > e[1]
                /\ \E x \in immediatelyCommitted : c = x.entry}

\* The set of prefix committed entries along with the term they were committed in.
PrefixCommittedEntriesWithTerm == 
    {   LET commitmentTerm == CHOOSE t \in 1..10 : 
            \E l \in Range(log) :
                /\ EntryInLog(l, e[1], e[2])
                /\ \E c \in LogEntries(l) :
                    /\ c[1] > e[1]
                    /\ [entry |-> c, term |-> t] \in immediatelyCommitted IN
         [entry |-> e, term |-> commitmentTerm]
        : e \in PrefixCommittedEntries}

\* The set of all committed log entries up to the current state. Note that this definition depends
\* on a history variable, 'immediatelyCommitted'. That history variable is constructed by appending the
\* immediately committed entries at every state to a set. So, at any one state, it should store the complete
\* set of entries that were ever immediately committed. Some entries may never be immediately committed and will
\* only get "prefix committed". 
CommittedEntries == immediatelyCommitted \cup PrefixCommittedEntriesWithTerm

\* Is 'xlog' a prefix of 'ylog'.
IsPrefix(xlog, ylog) == 
    /\ Len(xlog) <= Len(ylog)
    /\ xlog = SubSeq(ylog, 1, Len(xlog))

\* If two logs have the same last log entry term, then one is a prefix of the other. (Will is trying to see if 
\* this is actually true).
LastTermsEquivalentImplyPrefixes == 
    \A xlog, ylog \in allLogs :
        LastTerm(xlog) = LastTerm(ylog) =>
        IsPrefix(xlog, ylog) \/ IsPrefix(ylog, xlog)


(**************************************************************************************************)
(* The terms of every server increase monotonically.                                              *)
(*                                                                                                *)
(* We express this as an 'action' property.  That is, it depends on the both primed and unprimed  *)
(* variables.                                                                                     *)
(**************************************************************************************************)
TermsMonotonic == 
    [][\A s \in Server : currentTerm'[s] >= currentTerm[s]]_vars        

(**************************************************************************************************)
(* There should be at most one leader per term.                                                   *)
(**************************************************************************************************)
ElectionSafety == \A e1, e2 \in elections: 
                    e1.eterm = e2.eterm => e1.eleader = e2.eleader
                    
(**************************************************************************************************)
(* Leader logs should only ever grow.  This is defined as a temporal property i.e.  it depends on *)
(* the current and next state.                                                                    *)
(**************************************************************************************************)                    
LeaderAppendOnly == [][\A s \in Server : state[s] = Primary => Len(log'[s]) >= Len(log[s])]_vars

(**************************************************************************************************)
(* An <<index, term>> pair should uniquely identify a log prefix.                                 *)
(**************************************************************************************************)
LogMatching == 
    \A xlog, ylog \in allLogs : 
    Len(xlog) <= Len(ylog) =>
    \A i \in DOMAIN xlog : 
        xlog[i].term = ylog[i].term => 
        SubSeq(xlog, 1, i) = SubSeq(ylog, 1, i)
       
(**************************************************************************************************)
(* Only uncommitted entries are allowed to be deleted from logs.                                  *)
(**************************************************************************************************)    
RollbackSafety == 
    \E i,j \in Server : CanRollback(log[i], log[j]) =>
        LET commonPoint == RollbackCommonPoint(log[i], log[j])
            entriesToRollback == SubSeq(log[j], commonPoint + 1, Len(log[j])) IN
            \* The entries being rolled back should NOT be committed.
            entriesToRollback \cap CommittedEntries = {}     


(**************************************************************************************************)
(* If an entry was committed, then it must appear in the logs of all leaders of higher terms.     *)
(**************************************************************************************************)
LeaderCompleteness == 
 \A e \in CommittedEntries :
 \A election \in elections:
    LET index == e.entry[1] 
        term == e.entry[2] IN
    election.eterm > e.term => EntryInLog(election.elog, index, term)

(**************************************************************************************************)
(* If the 'commitIndex' on any server includes a particular log entry, then that log entry must   *)
(* be committed.  To generalize the approach of basic Raft, we store commitIndex as an <<index,   *)
(* term>> pair, instead of just an index.  That way we can store information about the commit     *)
(* point even if if our log doesn't contain the committed entries.  An <<index,term>> pair should *)
(* uniquely identify a log prefix (Log Matching), so a commitIndex being at <<index, term>>       *)
(* indicates that that unique log prefix is committed.                                            *)
(**************************************************************************************************)  
LearnerSafety == 
    \A s \in Server :
    \* If the commit point exists in the node's log, then it should contain
    \* all committed entries. Otherwise, it is not necessary to contain the committed
    \* entries.
    EntryInLog(log[s], commitIndex[s][1], commitIndex[s][2]) =>
        \A i \in DOMAIN log[s] : i < commitIndex[s][1] =>
            \E c \in CommittedEntries : <<i, log[s][i].term>> = c.entry

\*
\* Liveness Properties (Experimental)
\*

\* Eventually all servers store the same logs forever. This should only be true 
\* in the absence of new client requests, but if the maximum log length of 
\* servers is limited in a model, then logs should eventually converge, since new client
\* requests will eventually be disallowed.
EventuallyLogsConverge == <>[][\A s, t \in Server : s # t => log[s] = log[t]]_vars

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* "Sanity Check" Properties                                                                      *)
(*                                                                                                *)
(* These are not high level correctness properties of the algorithm, but important properties     *)
(* that should hold true if we wrote the spec and the correctness properties correctly.           *)
(**************************************************************************************************)

\* The set of prefix committed entries should only ever grow. Entries should never be deleted
\* from it.
PrefixCommittedEntriesMonotonic == 
    [][(PrefixCommittedEntriesWithTerm \subseteq PrefixCommittedEntriesWithTerm')]_<<vars>>

\* The set of committed entries should only ever grow. Entries should never be deleted
\* from it.
CommittedEntriesMonotonic == 
    [][(CommittedEntries \subseteq CommittedEntries')]_<<vars>>
    
\* Immediately committed entries <<index, T>> are always committed at term T.
ImmediatelyCommittedTermMatchesLogEntryTerm == 
    \A e \in immediatelyCommitted : e.entry[2] = e.term
   
\* Eventually logs grow to include some entries.
EventuallyLogsNonEmpty == <>(\E s \in Server : Len(log[s]) > 0)


-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Spec definition                                                                                *)
(**************************************************************************************************)
    
InitHistoryVars == 
    /\ elections = {}
    /\ allLogs   = {log[i] : i \in Server}
    /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
    /\ immediatelyCommitted = {}
    
InitServerVars == 
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ votedFor    = [i \in Server |-> Nil]
    /\ matchEntry = [i \in Server |-> [j \in Server |-> <<0, 0>>]]

InitCandidateVars == 
    /\ votesResponded = [i \in Server |-> {}]
    /\ votesGranted   = [i \in Server |-> {}]
                     
InitLogVars == 
    /\ log          = [i \in Server |-> << >>]
    /\ commitIndex  = [i \in Server |-> <<0, 0>>]
    
Init == 
    /\ InitLogVars
    /\ InitHistoryVars
    /\ InitServerVars
    /\ InitCandidateVars
    /\ messages = {}

\* Next state predicate for history and proof variables. We (unfortunately) add it to every next-state disjunct
\* instead of adding it as a conjunct with the entire next-state relation because it makes for clearer TLC 
\* Toolbox error traces i.e. we can see what specific action was executed at each step of the trace. 
HistNext == 
    /\ allLogs' = allLogs \cup {log[i] : i \in Server}
    /\ immediatelyCommitted' = immediatelyCommitted \cup AllImmediatelyCommitted'
         
Next == 
    \/ \E s \in Server : BecomePrimary(s)                        /\ HistNext
    \/ \E s \in Server : Timeout(s)                              /\ HistNext
    \/ \E s \in Server : RequestVotes(s)                         /\ HistNext
    \/ \E s,t \in Server : HandleRequestVoteRequest(s, t)        /\ HistNext
    \/ \E s,t \in Server : HandleRequestVoteResponse(s, t)       /\ HistNext
    \/ \E s \in Server : \E v \in Value : ClientRequest(s, v)    /\ HistNext
    \/ \E s,t \in Server : SendEntries(s)                        /\ HistNext
    \/ \E s,t \in Server : HandleSendEntries(s)                  /\ HistNext
    \/ \E s,t \in Server :
        /\ EnableRollbackProtocol /\ RollbackEntries(s, t)       /\ HistNext   
    \/ \E s,t \in Server :
        /\ EnableLearnerProtocol  /\ UpdatePosition(s, t)        /\ HistNext 
    \/ \E s \in Server : 
        /\ EnableLearnerProtocol  /\ AdvanceCommitPoint(s)       /\ HistNext 

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* State Constraint. Used for model checking only.                                                *)
(**************************************************************************************************)

CONSTANTS MaxTerm, MaxLogLen

StateConstraint == \A s \in Server : 
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen
        
MaxTermInvariant ==  \A s \in Server : currentTerm[s] <= MaxTerm    
LogLenInvariant ==  \A s \in Server  : Len(log[s]) <= MaxLogLen    

-------------------------------------------------------------------------------------------

\*
\*        
\* Various interesting properties to check and to help debug the spec. Some are experimental.
\*
\*

\* There is an entry that exists on a majority of nodes but is not committed.
P1 == \E e \in AllLogEntries(Range(log)) :
      \E Q \in Quorum :
        /\ \A s \in Q : EntryInLog(log[s], e[1], e[2])
        /\ ~\E x \in immediatelyCommitted : x.entry = e

SyncSourceCyclePreCond == 
    \E s, t \in Server : 
        /\ commitIndex[s][1] > commitIndex[t][1]
        /\ commitIndex[s][1] > 0 /\ commitIndex[t][1] > 0
        /\ IsPrefix(log[s], log[t]) /\ Len(log[s]) < Len(log[t])
        
\* Experimental definition of immediately committed using temporal logic formula 
\* i.e. a predicate over an entire behavior.
\*ImmediatelyCommittedTemporal(e) == 
\*    \E Q \in Quorum : 
\*    \A s \in Q :
\*        <> (EntryInLog(log[s], e[1], e[2]) /\ currentTerm[s] = e[2])

\*ImmediatelyCommittedTemporal(e) == 
\*    \E s \in Server :
\*        <> (EntryInLog(log[s], e[1], e[2]) /\ currentTerm[s] = e[2])

ImmediatelyCommittedTemporal(e) == 
\*    \E s \in Server :
        <> (\E s \in Server : currentTerm[s] = e[2])

\*    AllLogEntries(Range(log))


=============================================================================
\* Modification History
\* Last modified Fri Feb 15 21:58:44 EST 2019 by williamschultz
\* Last modified Sun Jul 29 20:32:12 EDT 2018 by willyschultz
\* Created Mon Apr 16 20:56:44 EDT 2018 by willyschultz
