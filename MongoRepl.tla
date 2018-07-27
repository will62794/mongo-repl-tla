----------------------------- MODULE MongoRepl -----------------------------

\* A high level specification of the MongoDB replication protocol.

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

----
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

----
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

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))
    
\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----

(**************************************************************************************************)
(* Correctness Properties                                                                         *)
(**************************************************************************************************)


\* The set of all log entries for a given log i.e. the set of all <<index, term>>
\* pairs that appear in the log.
LogEntries(xlog) == {<<i, xlog[i].term>> : i \in DOMAIN xlog}

\* The set of all log entries (<<index, term>>) that appear in any log in the given log set.
AllLogEntries(logSet) == UNION {LogEntries(l) : l \in logSet}      

\* Determines whether an <<index, term>> entry is immediately committed, based on the
\* current state.
ImmediatelyCommitted(index, term) == 
    \E Q \in Quorum :
        \A q \in Q : 
            /\ currentTerm[q] = term 
            /\ \E i \in DOMAIN log[q] : i=index /\ log[q][i].term = term

\* The set of all 'immediately committed' log entries in the given set of logs.
AllImmediatelyCommitted(logSet) == {e \in AllLogEntries(logSet) : ImmediatelyCommitted(e[1], e[2])}

\* Is <<index, term>> in the given log.
EntryInLog(xlog, index, term) == \E i \in DOMAIN xlog : <<index, term>> = <<i, xlog[i].term>> 

ElectionSafety == \A e1, e2 \in elections: 
                    e1.eterm = e2.eterm => e1.eleader = e2.eleader

\* An <<index, term>> pair should uniquely identify a log prefix.
LogMatching == 
    \A xlog, ylog \in allLogs : 
    Len(xlog) <= Len(ylog) =>
    \A i \in DOMAIN xlog : 
        xlog[i].term = ylog[i].term => 
        SubSeq(xlog, 1, i) = SubSeq(ylog, 1, i)

\* If an entry was immediately committed at term T, then it must appear in the logs of all 
\* leaders of higher terms.
LeaderCompleteness == 
 \A <<index,term>> \in immediatelyCommitted :
 \A election \in elections:
    election.eterm > term => EntryInLog(election.elog, index, term)

\* If the 'commitIndex' on any server includes a particular log entry,
\* then that log entry must be committed.    
LearnerSafety == 
    \A s \in Server :
    \A i \in DOMAIN log[s] :
        i < commitIndex[s] =>
        <<i, log[s][i].term>> \in immediatelyCommitted

-----

(**************************************************************************************************)
(* Helper Operators                                                                               *)
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
    
    
(**************************************************************************************************)
(* Main Actions                                                                                   *)
(**************************************************************************************************)    

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
    

\* Node j removes entries based against the log of node i.
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
    
\* This property asserts that only uncommitted entries will ever be rolled back.
RollbackSafety == 
    \E i,j \in Server : CanRollback(log[i], log[j]) =>
        LET commonPoint == RollbackCommonPoint(log[i], log[j])
            entriesToRollback == SubSeq(log[j], commonPoint + 1, Len(log[j])) IN
            \* The entries being rolled back should NOT be committed.
            entriesToRollback \cap immediatelyCommitted = {}
                

\* Node i gets a new log entry from node j.
GetEntries(i, j) == 
    \* Node j must have more entries than node i.
    /\ Len(log[j]) > Len(log[i])
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
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex>>

QuorumAgreeInSameTerm(appliedEntryVal) == 
    LET quorums == {Q \in Quorum :
                    \* Make sure all nodes in quorum have actually applied some entries.
                    /\ \A s \in Q : appliedEntryVal[s][1] > 0
                    \* Make sure every applied entry in quorum has the same term.
                    /\ \A s, t \in Q : 
                       s # t => appliedEntryVal[s][2] = appliedEntryVal[t][2]} IN
        IF quorums = {} THEN Nil ELSE CHOOSE x \in quorums : TRUE

\* Naive (and quite possibly incorrect) approach. Calculate the commit point purely based on
\* the values in your current 'appliedEntry' vector. Choose the highest index
\* that is agreed upon by a majority. We are only allowed to choose a quorum
\* whose last applied entries have the same term.
AdvanceCommitPoint(i) == 
    LET quorumAgree == QuorumAgreeInSameTerm(appliedEntry[i]) IN
        /\ quorumAgree # Nil
        \* The term of the entries in the quorum must match our current term.
        /\ LET serverInQuorum == CHOOSE s \in quorumAgree : TRUE
               termOfQuorum == appliedEntry[i][serverInQuorum][2] IN
               termOfQuorum = currentTerm[i]
        \* Choose the minimum index of the applied entries in the quorum.
        /\ LET newCommitIndex == Min({appliedEntry[i][s][1] : s \in quorumAgree}) IN
           commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, appliedEntry>>           
    
\* Node i updates node j with its latest progress.
UpdatePosition(i, j) == 
    /\ Len(log[i]) > 0
    \* If node 'j' gives a progress update to node 'i', it must make sure to
    \* update the term of node 'i' with its own term, if it is higher. In a real system,
    \* this action would occur by 'j' sending a progress update message to 'i' that includes 
    \* the term of 'j' at the time of sending. Upon receiving the message, 'i' would update its
    \* own term if it was smaller than the term attached to the message.
    /\ currentTerm' = [currentTerm EXCEPT ![j] = Max({currentTerm[i], currentTerm[j]})]
    /\ LET lastEntry == <<Len(log[i]), LastTerm(log[i])>> IN
           /\ appliedEntry[j][i] # lastEntry \* Only update progress if newer.
           /\ appliedEntry' = [appliedEntry EXCEPT ![j][i] = lastEntry] 
    /\ UNCHANGED <<messages, state, votedFor, candidateVars, logVars, leaderVars, commitIndex>>           
    
\* Node i times out and automatically becomes a leader, if eligible.
BecomeLeader(i) == 
    LET voters == {s \in Server : CanVoteFor(s, i)}
        newTerm == currentTerm[i] + 1 IN
        /\ voters \in Quorum
        \* Update the terms of each voter.
        /\ currentTerm' = [s \in Server |-> IF s \in voters THEN newTerm ELSE currentTerm[s]]
        /\ votedFor' = [s \in Server |-> IF s \in voters THEN i ELSE votedFor[s]]
        /\ state' = [s \in Server |-> 
                        IF s = i THEN Primary
                        ELSE IF state[s] = Primary THEN Secondary \* Previous primaries should revert to secondary state.
                        ELSE state[s]] 
        /\ LET election == [eterm     |-> newTerm,
                            eleader   |-> i,
                            elog      |-> log[i],
                            evotes    |-> voters,
                            evoterLog |-> voterLog[i]] IN
           elections'  = elections \cup {election}        
        /\ UNCHANGED <<messages, logVars, candidateVars, appliedEntry>>
        
\* Node i, which must be a primary, handles a new client request and places the entry in its log.
ClientRequest(i, v) == 
    /\ state[i] = Primary
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> v]
       newLog == Append(log[i], entry) IN
       /\ log' = [log EXCEPT ![i] = newLog]
       /\ appliedEntry' = [appliedEntry EXCEPT ![i][i] = <<Len(newLog), entry.term>>]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex>>

    
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
    /\ commitIndex  = [i \in Server |-> 0]
    
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
    /\ immediatelyCommitted' = immediatelyCommitted \cup AllImmediatelyCommitted(allLogs)'
         
Next == 
    \/ \E s \in Server : BecomeLeader(s)                         /\ HistNext
    \/ \E s \in Server : \E v \in Value : ClientRequest(s, v)    /\ HistNext
    \/ \E s, t \in Server : GetEntries(s, t)                     /\ HistNext
    \/ \E s, t \in Server : RollbackEntries(s, t)                /\ HistNext
    \/ \E s, t \in Server : UpdatePosition(s, t)                 /\ HistNext
    \/ \E s \in Server : AdvanceCommitPoint(s)                   /\ HistNext

Spec == Init /\ [][Next]_vars

-----

\* State Constraint (used for model checking only).

MaxTerm == 4
MaxLogLen == 3
StateConstraint == \A s \in Server : 
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen
        
        

=============================================================================
\* Modification History
\* Last modified Thu Jul 26 22:50:25 EDT 2018 by williamschultz
\* Last modified Mon Apr 16 21:04:34 EDT 2018 by willyschultz
\* Created Mon Apr 16 20:56:44 EDT 2018 by willyschultz
