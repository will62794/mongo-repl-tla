# Todo Items

[X] Add a notion of entries being "committed at a term t". For example, for prefix committed entries, the
term of the entry itself may be different from the term at which it is committed. The "commitment term" is
what's important for the Leader Completeness Property. That is, an entry committed at term t is guaranteed
to appear in the logs of all future leaders with terms > t. It does not mean that all leaders with terms greater
than the _term of the committed entry_ necessarily contain the entry.

[ ] Add proper type invariants

[ ] Add a StateMachineSafety correctness property

[ ] Factor out correctness properties into their own module

# Logbook

### August 18, 2018

MaxTerm=3, MaxLogLen=3

- 57,166 distinct states found
- Depth of the complete state graph search is 18
- Finished in 7s, using 10 cores on Linux workstation

MaxTerm=4, MaxLogLen=3

- 473,054 distinct states found
- Depth of the complete state graph search is 26
- Finished in 46s, using 12 cores on Linux workstation

MaxTerm=5, MaxLogLen=3

- 12,799,316 distinct states found
- Depth of the complete state graph search is 39
- Finished in 21min 36s, using 10 cores on Linux workstation

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

### February 7, 2019

Trying to add commit point propagation to secondaries via SendEntries to reproduce a trace that could lead to a sync source cycle bug as seen in a test case failure. Want to demonstrate a case where A.lastApplied > B.lastApplied but A.lastCommitted < B.lastCommitted, which can be a pre-condition for sync source cycle when using commit point to consider who you sync from.

### February 9, 2019

Thinking about how to simplify the specification of "immediately committed" by utilizing a temporal logic formula. Trying to initially verify some of my assumptions about the meaning of certain temporal logic formulas in simpler cases before applying it to the repl protocol.  I believe that the correct temporal logic construction is to say that eventually, some quorum of servers have the appropriate state i.e. a log entry `<<index, term>>` when their local term is the same as the entry's. So, we could define an entry as being immediately committed as:

```
ImmediatelyCommitted(e) == ∀ s ∈ Quorum : ◇ HasLogEntryWhileInTerm(e)
```

That is, the entry doesn't have to be in the right state on each server in a quorum at the _same_ time, it only needs to be in the state at _some_ time, for each server in the quorum. Next I would like to verify that this definition implies the other definition of immediately committed that I already have defined in the spec.

### February 10, 2019

Going to try to model check the new temporal logic version of "immediately committed", to see if it aligns with my expectations. Goal: try to verify that the temporal logic definition matches the history state formulation already written i.e. the `immediatelyCommited` history variable that stores the set of all immediately committed log entries.

To start, I will try to generate some non-trivial trace, and then use the Trace Explorer to evaluate the definition of immediately committed for a single entry at each trace step. I think the Trace Explorer should work even for a temporal formula? Maybe it only works for state expressions.

Another simple invariant to get a good trace: just check that `immediatelyCommitted = {}`. This should fail with a trace that commits some entry.

Yep, the trace explorer cannot evaluate temporal formulas. It gave an explicit error message saying so. Instead, how about trying to just add a property that a certain entry never becomes immediately committed (with new temporal definition), and having the model checker produce a trace that violates it.

Realized that the state space may have enlarged since I added commit point propagation on secondaries that is *not* disabled even when learner protocol is turned off. For now I am commenting out the part where we update commit point on secondaries to keep state space theoretically same as it was before.

Giving a quick short at ad hoc TLC distributed mode to run models on Linux workstation. Network doesn't seem to be cooperating, so not continuing with this. 

Instead, going to try to re-run model without commit point propagation to get a baseline of model size. Then I can try turning on verification of the immediately committed temporal property. I think the model size may have grown a lot since I made RequestVote and SendEntries fully message based.

With MaxTerm=3, MaxLogLen=3:

- Reached 1,918,819 distinct states, diameter 29
- Queue size around 167, 000, and was decreasing at this point, but slowly
- Stopped model checker at this point after around 14-15 minutes running

With MaxTerm=2, MaxLogLen=2:

- 23,193 distinct states, diameter 27 
- Much more manageable!
- Ran in around 30 seconds.

Able to run the entire model with smaller parameters (MaxTerm=2, MaxLogLen=2) and check the new temporal property, but it's not producing a violation when I would expect. Need to understand why. 

Trying a more basic check i.e. does there exists _one_ server that had a particular entry while it was in the right term.

```tla
ImmediatelyCommittedTemporal(e) == 
    \E s \in Server :
        <> (EntryInLog(log[s], e[1], e[2]) /\ currentTerm[s] = e[2])
```

When checking that `~ImmediatelyCommittedTemporal(<<1,1>>)`, still didn't produce a violation. Now an even simpler version:

```tla
ImmediatelyCommittedTemporal(e) == 
    \E s \in Server :
        <> (currentTerm[s] = e[2])
```

TLC still doesn't produce a violation. 

I need to go back to basics with a very simple spec to make sure I understand semantics of temporal logic formulas and their potential interaction with state constraints. 

In summary, there is some tricky business regarding checking temporal properties/liveness while using state constraints. I can't say I fully grasp the issues here but it is touched upon in Section 14.3.5 of Specifying Systems. I may come back to this issue but I don't really feel like going down a big temporal logic rabbit hole just to come up with an alternate specification for "immediately committed". If possible, I would like to be confident in a temporal logic specification of immediately committed, but it may also make sense to just use a history variable to specify it. As a general note, it feels like history variables are often much simpler than reasoning about temporal logic and seem to often achieve the same thing. Perhaps history variables can't always express everything temporal logic does (?) but they sure seem very useful.

It seems like I should disable commitIndex advancement via SendEntries on secondaries when LearnerProtocol is disabled, but actually it might not matter since primaries won't advance the commit point when the protocol is disabled. I would still like to do another full model run with MaxTerm=3, MaxLogLen=3 and the latest message passing specification to get a baseline.

#### New Linux Workstation Model Checking Results

Sync Toolbox spec and model files to remote machine:

```
scp -r MongoRepl/*.{tla,cfg} wills-ubuntu:/ssd2/mongodb/tools/tlc/mongorepl/MongoRepl
```

##### Model: MaxTerm=3, MaxLogLen=2

Model checking `MongoRepl` with no rollback or learner protocol on Linux workstation:

- 309,577 distinct states
- Finished in 25s
- 10 TLC worker threads
- EnableRollbackProtocol=FALSE
- EnableLearnerProtocol=FALSE
- MaxTerm=3
- MaxLogLen=2

```
Starting... (2019-02-10 19:14:32)
Computing initial states...
Finished computing initial states: 1 distinct state generated.
Progress(17) at 2019-02-10 19:14:35: 253816 states generated (253,816 s/min), 39858 distinct states found (39,858 ds/min), 10871 states left on queue.
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 6.2E-8
  based on the actual fingerprints:  val = 1.1E-8
4007136 states generated, 309577 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 31.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 7 and the 95th percentile is 3).
Finished in 25s at (2019-02-10 19:14:57)
```

##### Model: MaxTerm=3, MaxLogLen=3

Model checking `MongoRepl` on Linux workstation:

- 30,874,412 distinct states
- Finished in 04min 05s
- 10 TLC worker threads
- EnableRollbackProtocol=FALSE
- EnableLearnerProtocol=FALSE
- MaxTerm=3
- MaxLogLen=3

```
Starting... (2019-02-10 19:18:38)
Computing initial states...
Finished computing initial states: 1 distinct state generated.
Progress(15) at 2019-02-10 19:18:41: 222031 states generated (222,031 s/min), 40798 distinct states found (40,798 ds/min), 14575 states left on queue.
Progress(24) at 2019-02-10 19:19:41: 8552528 states generated (8,330,497 s/min), 822612 distinct states found (781,814 ds/min), 174773 states left on queue.
Progress(27) at 2019-02-10 19:20:41: 16217310 states generated (7,664,782 s/min), 1392371 distinct states found (569,759 ds/min), 205638 states left on queue.
Progress(30) at 2019-02-10 19:21:41: 23516801 states generated (7,299,491 s/min), 1873466 distinct states found (481,095 ds/min), 172306 states left on queue.
Progress(35) at 2019-02-10 19:22:41: 30630471 states generated (7,113,670 s/min), 2226739 distinct states found (353,273 ds/min), 13455 states left on queue.
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 3.5E-6
  based on the actual fingerprints:  val = 1.8E-6
30874412 states generated, 2231545 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 38.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 9 and the 95th percentile is 3).
Finished in 04min 05s at (2019-02-10 19:22:44)
```

### Feburary 15, 2019

##### Model: MaxTerm=3, MaxLogLen=4

Model checking `MongoReplRollback` on Linux workstation:

- 21,872,209 distinct states
- Finished in 01h 12min
- 8 TLC worker threads
- EnableRollbackProtocol=TRUE
- EnableLearnerProtocol=FALSE
- MaxTerm=3
- MaxLogLen=4

```
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 3.6E-4
  based on the actual fingerprints:  val = 7.3E-4
321346532 states generated, 21872209 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 53.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 10 and the 95th percentile is 3).
Finished in 01h 12min at (2019-02-15 01:05:35)
```

I am working on a simplified version of the spec with coarser atomic actions. This is similar to how I originally started, and I am using an old Git revision of the original mongo spec. The simpler version will not model an async message passing system, and will let things like elections happen in a single atomic step. There have been a number of bugs in the replication system recently that have come up that are due to really interesting edge case behaviors, but many don't actually seem to depend on the fact that the system passes messages asynchronously. Perhaps a coarser, simpler model could serve to catch a lot of interesting bugs initially, before the need for a more complex, detailed spec that fully models the network, etc.

To make it more feasible to maintain two versions of a spec alongside each other, I think it would make sense to factor out the correctness property definitions into a separate file that can be imported by both e.g. `Properties.tla`. This will probably require parameterizing all of those definitions/operators strictly on their arguments, as opposed to referencing global state variables. This should allow them to be imported at the beginning of both specs and they won't need to reference variables that have not been declared yet.

I am currently trying to run the `MongoReplSimpler.tla` spec with a model of 5 nodes, MaxLogLen=4 and MaxTerm=3. I am letting this run on my Linux workstation to see how large the state space is. Then I will try to check some interesting invariants.

Don't forget to include the state constraint when model checking! Restarting the model run on workstation because the state constraint was not being imposed. Also forgot to make the server set a symmetry set.

### Feburary 16, 2019

Model checking completed overnight for the simpler model.

##### Model: MongoReplSimpler, MaxTerm=3, MaxLogLen=4

Model checking `MongoReplSimpler` on Linux workstation, with learner actions disabled:

- 150,125 distinct states
- Finished in 01min 02s
- 10 TLC worker threads
- MaxTerm=3
- MaxLogLen=4
- Server = `{n1,n2,n3,n4,n5}` (Symmetry Set)

```
TLC2 Version 2.12 of 29 January 2018
Running breadth-first search Model-Checking with 10 workers on 12 cores with 7143MB heap and 64MB offheap memory (Linux 4.8.0-59-generic amd64, Oracle Corporation 1.8.0_131 x86_64).
Parsing file /ssd2/mongodb/tools/tlc/mongorepl/MongoReplSimpler/MC.tla
Parsing file /ssd2/mongodb/tools/tlc/mongorepl/MongoReplSimpler/MongoReplSimpler.tla
Parsing file /ssd2/mongodb/tools/tlc/tla/tla2sany/StandardModules/TLC.tla                                                                                     Parsing file /ssd2/mongodb/tools/tlc/tla/tla2sany/StandardModules/Naturals.tla
Parsing file /ssd2/mongodb/tools/tlc/tla/tla2sany/StandardModules/Integers.tla
Parsing file /ssd2/mongodb/tools/tlc/mongorepl/MongoReplSimpler/FiniteSets.tla                                                                                Parsing file /ssd2/mongodb/tools/tlc/tla/tla2sany/StandardModules/Sequences.tla
Semantic processing of module Naturals
Semantic processing of module Integers
Semantic processing of module Sequences
Semantic processing of module FiniteSets                                                                                                                      Semantic processing of module TLC
Semantic processing of module MongoReplSimpler
Semantic processing of module MC
Starting... (2019-02-16 00:15:20)                                                                                                                             Computing initial states...
Finished computing initial states: 1 distinct state generated.                                                                                                Progress(14) at 2019-02-16 00:15:23: 46774 states generated (46,774 s/min), 7349 distinct states found (7,349 ds/min), 3148 states left on queue.
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.3E-8
  based on the actual fingerprints:  val = 7.5E-9
1689408 states generated, 150125 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 32.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 9 and the 95th percentile is 4).
Finished in 01min 02s at (2019-02-16 00:16:22)
```

Now that I have verified the underlying model's state space size, I am trying to check the property `NeverRollBackCommitted`, which states that it is impossible for a log entry to be committed and exist in a node's log, but be rolled back i.e. missing from that node's log in the next state. I am expecting this to be violated with a trace that leads to a case where this can happen. If no violation is found, I should go and double check my definition of the property. I have currently defined this property as follows:

```tla
\* Does there exist a server with a log entry 'e' such that e is committed but it subsequently rolls back?
RollBackCommitted ==
    ∃ s ∈ Server : 
    ∃ i ∈ DOMAIN log[s] : 
    ∃ e ∈ CommittedEntries :
        \* Entry is committed in the current state and in the log of 's'. 
        ∧ e.entry = <<i, log[s][i].term>>
        \* Entry is no longer in the log of 's' in the next state.
        ∧ ~EntryInLog(log'[s], i, log[s][i].term)
        
NeverRollBackCommitted == ~RollBackCommitted
```

*Important note*: Remember that apparently some liveness/property checking doesn't work correctly when symmetry sets are enabled in the model. I should be careful to turn these off before checking such "action properties" (which `NeverRollBackCommitted` is) to avoid potential false positives i.e. TLC not reporting an error when it should.

Ran the model without symmetry to check `NeverRollBackCommitted`. No violation found:

- 15,113,326 distinct states
- Finished in 04h 42min
- 10 TLC worker threads
- MaxTerm=3
- MaxLogLen=4
- Server = `{n1,n2,n3,n4,n5}`

```
Model checking completed. No error has been found.                                                                                                              Estimates of the probability that TLC did not check all reachable states                                                                                      because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.3E-4
  based on the actual fingerprints:  val = 3.2E-5
170289311 states generated, 15113326 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 32.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 9 and the 95th percentile is 4).                                            Finished in 04h 42min at (2019-02-16 15:26:24)
```

After thinking a bit more about the proposed scenario of rolling back a committed log entry, it seems possible with a maximum log length of 3. I will try to play around with the model checker to verify some other more basic assumptions about the spec to make sure the spec itself is actually accurate. 

I am curious if there are bugs surrounding checking action properties when using symmetry sets? If not, it would be nice to utilize the state space reduction of setting Server as a symmetry set.

I realized a potential issue with the `MongoReplSimpler.tla` spec that I overlooked. The currentTerm of every server starts at 1 i.e.

```tla
currentTerm = [i \in Server |-> 1]
```

So, the earliest term that a node can be elected is in term 2, since the first time a node runs for election it will bump its term. This means that with a state constraint restricting the max term N, we will get less than N elections. Going to fix this so that currentTerm of all servers starts at 0. I think this was already changed in `MongoRepl.tla`. I verified this by simply checking the negation of the following invariant:

```tla
IsLeader == \E s \in Server : state[s] = Primary
```

It is a simple way to see a trace with 1 election.

Another good sanity check is to make sure that you can see a trace where entries are "prefix committed". This can be easily checked with the invariant:

```tla
PrefixCommittedEntriesWithTerm = {}
```    

Question: Do the set of prefix committed entries and the set of immediately committed entries need to be disjoint? I don't think they have to be, based on the definition. If an entry earlier in the log becomes immediately committed and an entry later in the log also becomes immediately committed, then by definition the earlier one would also be prefix committed, in addition to being immediately committed. I think it's ok if these sets overlap. I would like to produce a specific behavior where they _are_ disjoint, though.

Ok, so I was able to produce a satisfactory trace that shows that "prefix committed" can contain an entry that is not contained in "immediately committed". This invariant works to produce the trace:

```tla
\* A state where the set of "prefix committed" and "immediately committed" entries are both non-empty
\* and the set of "prefix committed" entries is not a subset of "immediately committed" entries.
PrefixAndImmediatelyCommittedDiffer ==
    /\ PrefixCommittedEntriesWithTerm # {}
    /\ immediatelyCommitted # {}
    /\ ~ (PrefixCommittedEntriesWithTerm \subseteq immediatelyCommitted)
```

If entries are only ever directly "immediately committed", then I believe that "prefix committed" will always be a subset of the "immediately committed" entries, so I wanted to see a trace that violated this condition.

Now that I have resolved the issue with currentTerm starting too high, I am going to kick off another run on the Linux workstation.

Successfully hit the invariant! [This](https://github.com/will62794/mongo-repl-tla/blob/0e5949bfac05d9fac7276ad43c0dbd58463e42b3/traces/tlc_err_trace_never_rollback_committed.txt) is the trace. I need to check the error trace to make sure it is correct, but it is 13 steps long and at first glance appears to demonstrate the issue I was after i.e. a committed entry gets rolled back on some node.

See State 6 of trace. n3 gets log entry from n2 even though currentTerm[n2]=1 which is less than currentTerm[n3]=2. This wouldn't happen in Raft because n3 would reject messages from a lower term? But I wonder if this is essential to violating `NeverRollBackCommitted` or not. Trying to run the model checker after modifying `GetEntries` to only accept log entries from someone whose term is equal or higher than your own.

#### Thoughts on Abstracting the Protocol More
When I read through traces of the algorithm, I feel like the most important bit of state is the `log` of each server. The other pieces of state feels more and more like implementation details that act to construct logs that satisfy the correct properties. I am wondering if there would be a way to write a spec at an even higher level of abstraction whose only state is the `log` itself i.e. no terms, server states, etc. The job of the algorithm/specification would be to then construct logs on each server that satisfy the necessary correctness properties. Log Matching is obviously an easy property that comes to mind that only depends on the log state. What do the other properties mean if we forget about things like the current state (i.e. Primary/Secondary) of servers? State Machine Safety doesn't seem to depend on things other than the log, though it may depend on the history of states. Leader Completeness requires that all new leaders contain any committed log entries, but this is really just to service the State Machine Safety property i.e. to make sure that we don't erase committed entries. If we only have logs and no terms, how do define an entry as being "committed"? Maybe it's easy i.e. we just say it's committed if it appears in a log slot for which no other entry ever subsequently appears. Not sure where to go with this; perhaps the simplified form of the spec is already pretty close to the minimal "essence" of the protocol.

### Feburary 17, 2019

I ran the model again but modified `GetEntries` so that nodes can only receive entries from nodes with an equal or higher term than their own. The model checking completed without finding a violation of `NeverRollBackCommitted`. This was the model with 5 nodes (no symmetry set), MaxLogLen=3 and MaxTerm=3. Found 41,115,086 distinct states. 

```tla
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 8.9E-4
  based on the actual fingerprints:  val = 1.6E-4
439426111 states generated, 41115086 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 32.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 10 and the 95th percentile is 3).
Finished in 07h 59min at (2019-02-17 03:41:39)
```

### Feburary 18, 2019

Cleaning up some of the obsolete or unused variables in the MongoReplSimpler spec. Hopefully this should make it clearer and easier to understand. It is good to always establish a baseline model before refactoring i.e. see that a spec with a given model generates a given number of states without errors, and then start refactoring and re-run the model to make sure the results haven't changed. Obviously this doesn't work for all types of refactoring, but in this case I am removing old stuff without intending to change spec behavior.

### February 24, 2019

Upgraded TLA+ Toolbox to nightly 1.5.8 build to work with Java 11. 

Going to revise `BecomeLeader` in `MongoReplSimpler` so that a leader doesn't require the vote of *all* nodes when it runs an election. This was an oversight when originally writing this spec. The leader should be able to garner votes from any subset of eligible voters that form a quorum.

 Verifying that the state space is larger with the new changes than without them i.e. there should be more possible varieties of elections when a leader can garner any quorum, not just all nodes.
 
 Indeed, with the new changes, there are more distinct states. This makes sense.

- Requiring all nodes to vote for leader: 1066 distinct states, MaxTerm=2, MaxLogLen=2
- Requiring quorum of nodes to vote for leader: 2878 distinct states, MaxTerm=2, MaxLogLen=2, requiring any quorum of voters

I checked `ElectionSafety`, `LogMatching`, and `LeaderCompleteness` properties when running these models.

Going to try re-enabling the learner protocol to get a sense of the state space size. Starting with MaxTerm=2, MaxLogLen=2. Starting a run on Linux workstation with both `UpdatePosition` action and `AdvanceCommitPoint` enabled. Letting this model run. I would like to initially verify that the model is actually finite. 

The model has already run for ~2 minutes on my workstation. My intuition is that this is too slow. Going to try disabling the `AdvanceCommitPoint` action and only leave the `UpdatePosition` action. Starting a new run with this configuration.

Another idea: to test commit point propagation rules alone, would be to have the primary just magically advance its commit point based on the global set of committed entries tracked by history variables. Then this commit point could be propagated to other nodes but we wouldn't need to be depending on the correctness of `UpdatePosition` and commit point advancement calculations. We would only be testing the commit point propagation rules i.e. not commit point advancement rules e.g.

```tla
\* Version of commit point advancement on a primary that directly inspects the global history variables. This would
\* not be possible in a real implementation, but we can use to it test other aspects of protocol e.g. commit point 
\* propagation, without relying on the correctness of commit point advancement rules on primary. We simply advance the
\* commit point to the newest "committed" log entry globally.
AdvanceCommitPointOmniscient(i) == TRUE  (* TODO *) 
```

Ok, the model run with only `UpdatePosition` action enabled completed. It was slow:

`MongoReplSimpler`, with `UpdatePosition` enabled, `AdvanceCommitPoint` disabled, run on Linux workstation:

- MaxTerm = 2
- MaxLogLen = 2
- 2,013,886 distinct states
- Finished in 05min 35s
- 10 TLC worker threads

```tla
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.6E-6
  based on the actual fingerprints:  val = 8.2E-7
16992301 states generated, 2013886 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 22.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 10 and the 95th percentile is 3).
Finished in 05min 35s at (2019-02-24 11:56:23)
```

I should update `MongoReplSimpler.tla` so that learner protocol can be easily disabled.

Making an attempt at a definition of `AdvanceCommitPointOmniscient`. For now, starting with having primaries advance their commit to some immediately committed log entry that exists in their current log. This rules out advancement of commit index to prefix committed log entries but I don't think that primaries should ever advance commit point directly to prefix committed entries anyway. Might need to check that though. This is a basic start, though. Next, will add a simple commit point propagation action via `GetEntries`. Secondaries receiving log entries also update their commit index to that of the sender if it is newer than their own.

Verifying that secondaries can advance their commit point with simple invariant:

```tla
~(\E s \in Server : commitIndex[s][1] > 0 /\ state[s]=Secondary)
```

Better invariant i.e. verify that a secondary actually updates its commit point when it gets a new log entry:

```tla
~(\E s,t \in Server : 
	/\ commitIndex[s][1] > 0 
	/\ commitIndex[s]=commitIndex[t] 
	/\ state[s]=Primary 
	/\ state[t]=Secondary)
```

Working with slightly new definitions of learner safety:

```tla
\* Are all the entries with indices less than the current 'commitIndex' of a server 's' actually committed?
CommitIndexSafe(s) == 
    \A i \in DOMAIN log[s] :
        i < commitIndex[s][1] =>
        \E e \in CommittedEntries : <<i, log[s][i].term>> = e.entry

\* Checks commit index safety on all servers.
LearnerSafety2 == 
    \A s \in Server :
    CommitIndexSafe(s)
```

Trying out the `LearnerSafety2` invariant after adding commit point propagation into model. Ran the model with MaxTerm=2, MaxLogLen=2, Server={n1, n2, n3} successfully. Will try a run with 5 nodes on workstation. Found a violation of `LearnerSafety2` after checking back on the model run. The [trace](https://github.com/will62794/mongo-repl-tla/blob/0e5949bfac05d9fac7276ad43c0dbd58463e42b3/traces/tlc_learner_safety2_err_trace.txt) is 15 steps long and took ~53 minutes to generate.


