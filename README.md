# MongoDB Replication Protocol
This is a high level TLA+ specification of MongoDB's replication protocol, which is based on the Raft consensus algorithm. This spec tries to abstract the essential elements of MongoDB's protocol and demonstrate that it satisfies the same key safety properties as Raft.

The spec can be broken down into 4 main sub-protocols:

1. Elections
2. Log Transferral
3. Rollback
4. Learner Protocol

Each of these sub-protocols has actions associated with it, which are annotated with an `(ACTION)` specifier in the comments.

## The System and the Specification

Note that MongoDB's replication protocol appears to differ from Raft in a number of ways. For example, it utilizes a "pull-based" replication mechanism in contrast to Raft's push based system. When abstracting the system to a higher level, it is possible to see that these two approaches are not fundamentally different, and are able to provide same underlying safety guarantees. MongoDB's rollback protocol implementation is also an isolated subcomponent of the system, and we model that protocol similarly in this spec. Raft does not make the process of deleting entries so isolated, but rather incorporates it into the handling of AppendEntries messages by follower nodes. We separate it into its own distinct protocol so as to make it clear how it works and what is correctness properties are. This spec also allows certain protocol actions (rollback and learner actions) to be optionally disabled. This is to aid modularity and to also reduce model checking times when verifying properties that don't depend on the correctness of a certain sub-protocol.

### Understanding the Protocol

The basic Raft protocol consists of two message types, `AppendEntries` and `RequestVote`. The former deals with sending new log entries from leaders to followers, and the latter handles the process of getting new servers elected as leaders. The essential goal of Raft is to maintain a consistent distributed log between a set of servers. To do this, it must have a leader that accepts new client request, places these requests into an ordered log, and determines when such a log entry is "committed" i.e. durable within the server group. The Raft protocol can be partitioned into two main parts. The first part of the protocol is responsible for log maintenance. This entails "building" logs correctly and editing them to remove certain unwanted log entries. We can view this protocol as strictly responsible for either growing or truncating logs. The details of _how_ the logs are grown or truncated are important. The second aspect of the protocol is referred to as the "learner" protocol. It is the protocol that is responsible for propagating information about the _state_ of servers in the system. It does not modify any state related to logs or elections. In some sense it can be thought of as a "read only" protocol. It's main job is to propagate information about when log entries are "committed", which in Raft means that they will never be deleted from any log in the future. Breaking Raft down in this way can make it easier to understand its abstract core, and to see how it is possible to extend it with implementations that differ from the message patterns described in the original protocol.


#### Log Maintenance

The log maintenance aspect of Raft is relatively simple, and deals with two fundamental actions: growing logs and truncating logs. In addition to this, the _term_ value of each server must be maintained correctly. To understand this part of Raft, it is key to examine the correctness properties it must uphold. The _Log Matching_ property is a core property of this protocol because it enforces a strong requirement on the possible states of logs on servers in the system.


#### Learner Protocol

It is possible for Raft to _commit_ a log entry without _telling_ servers that that log entry committed. This is an important distinction to understand, and it forms the basis for the learner protocol being its own isolated set of rules/behavior. Raft provides a precise condition for when a log entry is _committed_, but there can be alternate ways a protocol decides to propagate such information. For Raft, the key definition is _immediately committed_. If a log entry becomes _immediately committed_, then it implies it is _committed_. The condition for a log entry being _immediately committed_ depends on the current, global state of the system. This global state is impossible to be directly viewed by any member of the system, but it is useful to define this condition in terms of a global state. An entry `e=(index, term)` is _immediately committed_ if a quorum of servers contain *e* and currentTerm[s]=term for all servers _s_ in this quorum. If such a state occurs, then an entry will be immediately commmitted, which implies it is committed. The learner protocol is resposible for correctly determining the existence of this global state by propagating messages between nodes. It must only tell a node that an entry has been commited if it has actuall has been. This is the protocol's key safety property. To do this, the protocol gossips the log application progress of a node to all other nodes. So, for example, if a node has applied up to entry e1, then it will send a message to some (or all) other nodes in the system informing them of this fact. When it propagates this information, it must be sure to include its own _term_ at the time of sending. This way, the node receiving such a message can know that the sender node applied up to entry e _while_ it was in a certain term, i.e. the term attached to the message. If it learns information about enough nodes (a quorum) applying an entry in the same term, then it can determine such an entry is immediately committed, and thus, committed.


Raft proof's definition of immediately commited:

```tla
immediatelyCommitted == 
	{ <<index, term>> ∈ anyLog :
		∧ anyLog ∈ allLogs
		∧ ∃ leader ∈ Server : subquorum ∈ SUBSET Server :
		∧ subquorum ∪ {leader} ∈ Quorum
		∧ ∀ i ∈ subquorum
			∃ m ∈ messages :
				∧ m.mtype = AppendEntriesResponse
				∧ m.msource = i
				∧ m.mdest = leader
				∧ m.mterm = term
				∧ m.mmatchIndex ≥ index
				
	}
```

This definition defines the set of all immediately committed entries. It is defined in terms of the state of the network i.e. the messages that are currently in transit. One way to view this is to think of it as describing a set of states that existed in the past. If a server has sent a message that now exists in the network, that message contains a subset of that server's state at the time it sent the message. So, some predicate that depends on that message's state can be seen as depending on a past state of that server.  There is one simple case where a set of entries are _immediately committed_, even though it is not the unique case. If there is a majority of servers who contain a particular log entry `<<index, ter>>` at the _same time_ and all have a currentTerm equal to that of the log entry, then that entry is immediately committed. In this scenario, we can more easily identify an immediately committed entry by examining a single global state. With the definition given above, all servers don't necessarily need to have the log entry and be in the right term at the same time, they just need to have been in the state at some point.

It is also important to point out that a particular entry being _immediately committed_ depends on the current state, and so it may be true in one state and false in the next. For example, if a majority of nodes send out response messages satisfying the definition above, but then one of the messages get dropped. The log entry was still immediately committed in one state, and therefore it should become committed. In the current state, after the message was dropped, however, it would not be immediately committed by the definition.

#### Historical Bug Analysis

SERVER-22136

SERVER-34728

