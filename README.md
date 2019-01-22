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

