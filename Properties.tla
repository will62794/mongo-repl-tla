---------------------------------------- MODULE Properties ----------------------------------------
\*
\* Correctness property definitions for the MongoDB replication protocol spec.
\*

EXTENDS Naturals

\* Prefix definitions to avoid name collisions while refactoring.

\* Return the range of a given function.
LOCAL Range(f) == {f[x] : x \in DOMAIN f}

\* The set of all log entries in a given log i.e. the set of all <<index, term>>
\* pairs that appear in the log.
___LogEntries(xlog) == {<<i, xlog[i].term>> : i \in DOMAIN xlog}

\* Is <<index, term>> in the given log.
___EntryInLog(xlog, index, term) == <<index, term>> \in ___LogEntries(xlog)

\* The set of all log entries (<<index, term>>) that appear in any log in the given log set.
___AllLogEntries(logSet) == UNION {___LogEntries(l) : l \in logSet}      

\* Determines whether an <<index, term>> entry is immediately committed, based on the
\* current state. Be careful to note that the value of this expression only depends on the current state, 
\* not the history of states. A particular entry may be immediately committed in the current state,
\* but not immediately committed in the next state. 
\* 'log' is the variable that stores the state of all node logs.
\* 'quorum' is the set of all server quorums.
\* 'currentTerm' is the variable that stores the current term of each server.
___ImmediatelyCommitted(log, currentTerm, quorum, index, term) == 
    \E Q \in quorum :
        \A q \in Q : 
            /\ currentTerm[q] = term
            /\ ___EntryInLog(log[q], index, term)

\* The set of all immediately committed log entries in the current state. An entry is committed
\* at a particular term t, so we store the entry itself along with the term at which it was committed. 
\* In general, the "commitment term" doesn't need to match the term of the entry itself, although for 
\* immediately committed entries, it will. It may not for prefix committed entries, though.
\* 'log' is the variable that stores the state of all node logs.
\* 'quorum' is the set of all server quorums.
\* 'currentTerm' is the variable that stores the current term of each server.
___AllImmediatelyCommitted(log, currentTerm, quorum) == 
    LET entries == {e \in ___AllLogEntries(Range(log)) : ___ImmediatelyCommitted(log, currentTerm, quorum, e[1], e[2])} IN
    {[entry |-> e, term |-> e[2]] : e \in entries}

\* The set of prefix committed entries.
\* 'immediatelyCommitted' is a history variable that stores the set of all immediately committed entries.
___PrefixCommittedEntries(log, immediatelyCommitted) == 
    {e \in ___AllLogEntries(Range(log)) :
        \E l \in Range(log) : 
            /\ ___EntryInLog(l, e[1], e[2])
            /\ \E c \in ___LogEntries(l) :
                /\ c[1] > e[1]
                /\ \E x \in immediatelyCommitted : c = x.entry}

\* The set of prefix committed entries along with the term they were committed in.
___PrefixCommittedEntriesWithTerm(log, immediatelyCommitted) == 
    {   LET commitmentTerm == CHOOSE t \in 1..10 : 
            \E l \in Range(log) :
                /\ ___EntryInLog(l, e[1], e[2])
                /\ \E c \in ___LogEntries(l) :
                    /\ c[1] > e[1]
                    /\ [entry |-> c, term |-> t] \in immediatelyCommitted IN
         [entry |-> e, term |-> commitmentTerm]
        : e \in ___PrefixCommittedEntries(log, immediatelyCommitted)}


====================================================================================================
\* Modification History
\* Last modified Fri Feb 15 22:05:47 EST 2019 by williamschultz
\* Created Fri Feb 15 21:47:13 EST 2019 by williamschultz
