----------------------------- MODULE MongoRepl -----------------------------
(**************************************************************************************************)
(* A high level specification of the MongoDB replication protocol.                                *)
(**************************************************************************************************)

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Secondary, Candidate, Primary

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

-------------------------------------------------------------------------------------------

\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another.
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

-------------------------------------------------------------------------------------------

\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm

\* The server's state (Follower, Candidate, or Leader).
VARIABLE state

\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor

\* A function maintained on each server that contains a local view of how far each node think
\* every other node has applied to in its log. Maps from server id to <<index, term>> tuple.
VARIABLE appliedEntry

serverVars == <<currentTerm, state, votedFor>>

\* A sequence of log entries. The index into this sequence is the index of the
\* log entry
VARIABLE log

\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:

\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded

\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted

\* A history variable used in the proof. This would not be present in an
\* implementation. It is a function from each server that voted for this candidate 
\* in its currentTerm to that voter's log.
VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted, voterLog>>

leaderVars == <<elections>>

vars == <<messages, allLogs, serverVars, candidateVars, leaderVars, logVars, appliedEntry, immediatelyCommitted>>

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

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Next state actions.                                                                            *)
(**************************************************************************************************)    

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Can node 'i' currently cast a vote for node 'j'.
CanVoteFor(i, j) == 
    LET logOk == 
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    /\ currentTerm[i] <= currentTerm[j]
    /\ j # votedFor[i] 
    /\ logOk
 
\* Could server 'i' win an election in the current state.
IsElectable(i) == 
    LET voters == {s \in Server : CanVoteFor(s, i)} IN
        voters \in Quorum

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
    

(**************************************************************************************************)
(* Node 'j' removes entries based against the log of node 'i'.                                    *)
(**************************************************************************************************)
RollbackEntries(i, j) == 
    /\ CanRollback(log[i], log[j])
    /\ LET commonPoint == RollbackCommonPoint(log[i], log[j]) IN
           \* If there is no common entry between log 'i' and
           \* log 'j', then it means that the all entries of log 'j'
           \* are divergent, and so we erase its entire log. Otherwise
           \* we erase all log entries after the newest common entry. Note that 
           \* if the commonPoint is '0' then SubSeq(log[i], 1, 0) will evaluate
           \* to <<>>, the empty sequence.
           log' = [log EXCEPT ![j] = SubSeq(log[i], 1, commonPoint)] 
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, appliedEntry>>
       

(**************************************************************************************************)
(* Node 'i' gets a new log entry from node 'j'.                                                   *)
(**************************************************************************************************)
GetEntries(i, j) == 
    /\ state[i] = Secondary
    \* Node j must have more entries than node i.
    /\ Len(log[j]) > Len(log[i])
    /\ currentTerm[j] >= currentTerm[i]
       \* log[i] is empty.
    /\ \/ /\ Len(log[i]) = 0
          /\ LET newEntry == log[j][1]
                 newLog   == Append(log[i], newEntry) IN
             /\ log' = [log EXCEPT ![i] = newLog]
             /\ appliedEntry' = [appliedEntry EXCEPT ![i][i] = <<Len(newLog), newEntry.term>>]
       \* log[i] is non-empty. In this case, the entry at the last
       \* index of node i's log must match the entry at the same index in node j's
       \* log. This is the essential 'log consistency check'.
       \/ /\ Len(log[i]) > 0
          /\ log[j][Len(log[i])] = log[i][Len(log[i])]
          /\ LET newEntry == log[j][Len(log[i]) + 1] 
                 newLog   == Append(log[i], newEntry) IN
                 /\ log' = [log EXCEPT ![i] = newLog]
                 /\ appliedEntry' = [appliedEntry EXCEPT ![i][i] = <<Len(newLog), newEntry.term>>]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[j]]
    /\ UNCHANGED <<messages, state, votedFor, candidateVars, leaderVars, commitIndex>>

QuorumAgreeInSameTerm(appliedEntryVal) == 
    LET quorums == {Q \in Quorum :
                    \* Make sure all nodes in quorum have actually applied some entries.
                    /\ \A s \in Q : appliedEntryVal[s][1] > 0
                    \* Make sure every applied entry in quorum has the same term.
                    /\ \A s, t \in Q : 
                       s # t => appliedEntryVal[s][2] = appliedEntryVal[t][2]} IN
        IF quorums = {} THEN Nil ELSE CHOOSE x \in quorums : TRUE

(**************************************************************************************************)
(* Naive (and quite possibly incorrect) approach.  Calculate the commit point purely based on the *)
(* values in your current 'appliedEntry' vector.  Choose the highest index that is agreed upon by *)
(* a majority.  We are only allowed to choose a quorum whose last applied entries have the same   *)
(* term.                                                                                          *)
(**************************************************************************************************)
AdvanceCommitPoint(i) == 
    LET quorumAgree == QuorumAgreeInSameTerm(appliedEntry[i]) IN
        /\ quorumAgree # Nil
        \* The term of the entries in the quorum must match our current term.
        /\ LET serverInQuorum == CHOOSE s \in quorumAgree : TRUE
               termOfQuorum == appliedEntry[i][serverInQuorum][2] 
               \* The minimum index of the applied entries in the quorum.
               newCommitIndex == Min({appliedEntry[i][s][1] : s \in quorumAgree}) IN
               /\ termOfQuorum = currentTerm[i]
               \* We store the commit index as an <<index, term>> pair instead of just an
               \* index, so that we can uniquely identify a committed log prefix.
               /\ commitIndex' = [commitIndex EXCEPT ![i] = <<newCommitIndex, termOfQuorum>>]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, appliedEntry>>           
    
(**************************************************************************************************)
(* Node 'i' updates node 'j' with its latest progress.                                            *)
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
           /\ appliedEntry[j][i] # lastEntry \* Only update progress if newer.
           /\ appliedEntry' = [appliedEntry EXCEPT ![j][i] = lastEntry] 
    /\ UNCHANGED <<messages, votedFor, candidateVars, logVars, leaderVars, commitIndex>>           
    
    
(**************************************************************************************************)
(* Node 'i' times out and automatically becomes a leader, if eligible.                            *)
(**************************************************************************************************)
BecomeLeader(i) == 
    LET voters == {s \in Server : CanVoteFor(s, i)}
        newTerm == currentTerm[i] + 1 IN
        /\ voters \in Quorum
        \* Update the terms of each voter.
        /\ currentTerm' = [s \in Server |-> IF s \in voters THEN newTerm ELSE currentTerm[s]]
        /\ votedFor' = [s \in Server |-> IF s \in voters THEN i ELSE votedFor[s]]
        /\ state' = [s \in Server |-> 
                        IF s = i THEN Primary
                        ELSE IF s \in voters THEN Secondary \* All voters should revert to secondary state.
                        ELSE state[s]] 
        /\ LET election == [eterm     |-> newTerm,
                            eleader   |-> i,
                            elog      |-> log[i],
                            evotes    |-> voters,
                            evoterLog |-> voterLog[i]] IN
           elections'  = elections \cup {election}        
        /\ UNCHANGED <<messages, logVars, candidateVars, appliedEntry>>
        
(**************************************************************************************************)
(* Node 'i', a primary, handles a new client request and places the entry in its log              *)
(**************************************************************************************************)        
ClientRequest(i, v) == 
    /\ state[i] = Primary
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> v]
       newLog == Append(log[i], entry) IN
       /\ log' = [log EXCEPT ![i] = newLog]
       /\ appliedEntry' = [appliedEntry EXCEPT ![i][i] = <<Len(newLog), entry.term>>]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex>>


-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Correctness Properties                                                                         *)
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

(**************************************************************************************************)
(* There should be at most one leader per term.                                                   *)
(**************************************************************************************************)
ElectionSafety == \A e1, e2 \in elections: 
                    e1.eterm = e2.eterm => e1.eleader = e2.eleader

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
        \A i \in DOMAIN log[s] :
            i < commitIndex[s][1] =>
            \E c \in CommittedEntries : <<i, log[s][i].term>> = c.entry

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
    /\ currentTerm = [i \in Server |-> 1]
    /\ state       = [i \in Server |-> Secondary]
    /\ votedFor    = [i \in Server |-> Nil]
    /\ appliedEntry = [i \in Server |-> [j \in Server |-> <<-1,-1>>]]

InitCandidateVars == 
    /\ votesResponded = [i \in Server |-> {}]
    /\ votesGranted   = [i \in Server |-> {}]
                     
InitLogVars == 
    /\ log          = [i \in Server |-> << >>]
    /\ commitIndex  = [i \in Server |-> <<0, 0>>]
    
Init == 
    /\ messages = [m \in {} |-> 0]
    /\ InitLogVars
    /\ InitHistoryVars
    /\ InitServerVars
    /\ InitCandidateVars

\* Next state predicate for history and proof variables. We (unfortunately) add it to every next-state disjunct
\* instead of adding it as a conjunct with the entire next-state relation because it makes for clearer TLC 
\* Toolbox error traces i.e. we can see what specific action was executed at each step of the trace. 
HistNext == 
    /\ allLogs' = allLogs \cup {log[i] : i \in Server}
    /\ immediatelyCommitted' = immediatelyCommitted \cup AllImmediatelyCommitted'
         
Next == 
    \/ \E s \in Server : BecomeLeader(s)                         /\ HistNext
    \/ \E s \in Server : \E v \in Value : ClientRequest(s, v)    /\ HistNext
    \/ \E s, t \in Server : GetEntries(s, t)                     /\ HistNext
    \/ \E s, t \in Server : RollbackEntries(s, t)                /\ HistNext
    \/ \E s, t \in Server : UpdatePosition(s, t)                 /\ HistNext
    \/ \E s \in Server : AdvanceCommitPoint(s)                   /\ HistNext

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* State Constraint. Used for model checking only.                                                *)
(**************************************************************************************************)

CONSTANTS MaxTerm, MaxLogLen

StateConstraint == \A s \in Server : 
                    /\ currentTerm[s] < MaxTerm
                    /\ Len(log[s]) < MaxLogLen
        
MaxTermInvariant ==  \A s \in Server : currentTerm[s] <= MaxTerm    
LogLenInvariant ==  \A s \in Server  : Len(log[s]) <= MaxLogLen    

=============================================================================
\* Modification History
\* Last modified Sat Aug 04 17:52:40 EDT 2018 by williamschultz
\* Last modified Sun Jul 29 20:32:12 EDT 2018 by willyschultz
\* Created Mon Apr 16 20:56:44 EDT 2018 by willyschultz
