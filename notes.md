# Todo Items

[X] Add a notion of entries being "committed at a term t". For example, for prefix committed entries, the
term of the entry itself may be different from the term at which it is committed. The "commitment term" is
what's important for the Leader Completeness Property. That is, an entry committed at term t is guaranteed
to appear in the logs of all future leaders with terms > t. It does not mean that all leaders with terms greater
than the _term of the committed entry_ necessarily contain the entry.

[ ] Add proper type invariants

[ ] Add a StateMachineSafety correctness property


# Model Checking Notes

August 18, 2018

MaxTerm=3
MaxLogLen=3
57,166 distinct states found
Depth of the complete state graph search is 18
Finished in 7s, using 10 cores on Linux workstation

MaxTerm=4
MaxLogLen=3
473,054 distinct states found
Depth of the complete state graph search is 26
Finished in 46s, using 12 cores on Linux workstation

MaxTerm=5
MaxLogLen=3
12,799,316 distinct states found
Depth of the complete state graph search is 39
Finished in 21min 36s, using 10 cores on Linux workstation

# Logbook

### December 29, 2018

Added the ability to explicitly disable/enable the learner and/or rollback protocols
by setting the value of a CONSTANT in the spec. This allows different models to turn these protocols
on or off. Experimenting with model checking the core protocol + rollback protocol
to check all key safety properties.

Discovered bug in spec where LogMatching is violated if we forget to limit RollbackEntries action to 
only occur on secondaries. Should add a LeaderAppendOnly safety property.

### January 1, 2019

To reduce model checking state space, don't need to send an empty log in the SendEntries action. I think
this can be added as an optimization in the model, not in the spec though.

### January 15, 2019

- Is it possible that turning ON the RollbackProtocol can lead to a smaller state space than if we turn OFF
the RollbackProtocol?

I think that sending out votes all at once is a fine simplification to make and it reduces model checking state space. I think it might be cleanest to model elections for candidates as simply sending out all vote messages once and waiting to hear back, but never sending out messages again. This could serve as one model of elections i.e. you try once and if you fail you just give up until you either timeout again or revert to secondary.

Wondering if it's possible to have two alternative versions of LearnerProtocol. For primaries, their learner protocol involves learning information from secondaries about their lastApplied optimes. It needs to know if a majority of them applied up to a certain optime while they were in the same term as that primary. For secondaries to advance their commit point, though, they get it from other nodes, who ultimately get it from the primary. When primaries advance their commit point, they follow rules of UpdatePosition learner protocol, which can be shown correct. Secondaries can retrieve the commit point from a primary if they know their current log is a prefix of the primary. Similarly, other secondaries can retrieve the commit point from a secondary their log is a prefix of. Perhaps this rule is satisfactory for secondaries to safely advance their optimes. We perhaps could additionally extend the LearnerProtocol to allow secondaries to advance the commit point of their own accord, without needing to let the primary do it.

### January 16, 2019

Might be able to simplify the definition of LearnerSafety if we assume LogMatching. We could check only that the latest optime is in the set of committed entries instead of every log entry.

Understand why we can't have 3 elections even when MaxTerm==3.

### January 21, 2019

I think I will simplify the learner protocol for now to only advance the commitIndex on primary nodes. Eventually it should be OK to generalize it so secondaries can also advance commit point by same mechanism, but to start we can have them advance commit point by receiving updates along with `SendEntries` messages. 

While exploring the correctness of LearnerSafety, I noticed a bug that violates the property if `SendEntries` messages don't include the term of the sender and update the recipient's term accordingly. For example, if a primary in term 1 sends log entries (in term 1) to a node in term 0, but doesn't update that node's term. That node is stuck in term 0, so by Raft's standard definition of *immediately committed*, that entry is not committed. The secondary would have to be in term 1. What are the implications of this? First of all, if secondaries don't update their term when they receive log entries from a primary, then it makes it hard for those entries to become committed, because the secondaries need some way of updating their term to actually get the entries immediately committed. The reasoning behind the definition of immediately committed, though, is to some extent about making sure enough nodes got the entry in a high enough term so they cannot vote for a newer primary that would delete the entry. If a log entry in term 1 is replicated to a primary and a secondary (out of 3 nodes) but the secondary is in term 0, is this a problem? The secondary could still vote for some primary in term 1, but the election rules guarantee that there isn't going to be any other primary in term 1, because we already have one, which we know since there was a log entry created in term 1. 

Maybe the definition of *immediately committed* could be extended. (It still seems like secondaries should be moving their term forward when they receive log entries, for the sake of liveness, even if it's not absolutely necessary.) The alternate definition of *immediately committed* might allow for an entry `<index, term>` to be *immediately committed* if there exists a majority of nodes that have the entry in their log and have a current term <= the term of the log entry. The existing definition requires that their current term is *equal* to the term of the log entry i.e. the term of the primary that created the entry.



