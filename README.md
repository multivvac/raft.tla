
Formal TLA+ specification for the [Raft consensus algorithm](https://raftconsensus.github.io). This is slightly updated compared to the dissertation version.

For more information, see Chapter 8 (Correctness) and Appendix B (Safety proof and formal specification) in https://github.com/ongardie/dissertation .

If you're trying to run the TLA+ model checker on this specification, check out Jin Li's changes in [Pull Request #4](https://github.com/ongardie/raft.tla/pull/4/).

Copyright 2014 Diego Ongaro.

This work is licensed under the Creative Commons Attribution-4.0 International License https://creativecommons.org/licenses/by/4.0/ .

Modified by Ovidiu Marcu

How to run?

The following runs with Restart, DuplicateMessage and DropMessage disabled.

1)
You can run one configuration see raft.cfg with: ./tlc.py --coverage 1 mc raft.tla, at latest commit.


49455516 states generated, 6425257 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 49.
Finished in 03min 22s at (2025-03-26 10:21:14)

My configuration:
Running breadth-first search Model-Checking with 32 workers on 32 cores with 7282MB heap and 4096MB offheap memory [pid: 1231] (Linux 5.15.167.4-microsoft-standard-WSL2 amd64, Ubuntu 11.0.26 x86_64, MSBDiskFPSet, DiskStateQueue).

When enabling Restart:
Progress(38) at 2025-03-26 10:49:32: 226,554,224 states generated (15,125,945 s/min), 32,923,274 distinct states found (1,987,637 ds/min), 7,516,412 states left on queue. and keeps running..
OR 

2)
model check the following with the Toolbox:

State constraint for model checking

(\A i \in Server: currentTerm[i] <= 2 /\ Len(log[i]) <= 2 ) /\ (\A m \in DOMAIN messages: messages[m] <= 1) /\ LeaderCountInv

Disable Profiling in TLC Options. See screenshots, raft.cfg for initializing model and expected results.

TLC command line parameters: -coverage 1

INVARIANTS
    MoreThanOneLeaderInv
    LogMatchingInv
    LeaderCompletenessInv
    LogInv
    MaxCInv
    LeaderCountInv
    MaxTermInv

My model

---- MODULE MC ----
EXTENDS raft, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1
----

\* MV CONSTANT definitions Server
const_1742979488646140000 == 
{r1, r2, r3}
----

\* MV CONSTANT definitions Value
const_1742979488646141000 == 
{v1}
----

\* SYMMETRY definition
symm_1742979488646142000 == 
Permutations(const_1742979488646140000)
----

\* CONSTANT definitions @modelParameterConstants:10MaxClientRequests
const_1742979488646143000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:11MaxBecomeLeader
const_1742979488646144000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:12MaxTerm
const_1742979488646145000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1742979488646146000 ==
(\A i \in Server: currentTerm[i] <= 2 /\ Len(log[i]) <= 2 ) /\ (\A m \in DOMAIN messages: messages[m] <= 1) /\ LeaderCountInv
----
=============================================================================
\* Modification History
\* Created Wed Mar 26 09:58:08 CET 2025 by ovidiu-cristian.marc

CASE MyInit

Finding a trace with LeaderCommited violated.

<<
[
 _TEAction |-> [
   position |-> 1,
   name |-> "Initial predicate",
   location |-> "Unknown location"
 ],
 allLogs |-> {<<>>},
 commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> << >>,
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> (r1 :> <<>> @@ r2 :> <<>> @@ r3 :> <<>>),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 0,
 messages |-> << >>,
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
],
[
 _TEAction |-> [
   position |-> 2,
   name |-> "Next",
   location |-> "line 567, col 9 to line 581, col 58 of module raft"
 ],
 allLogs |-> {<<>>},
 commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> (<<1, 2>> :> [sentCount |-> 0, ackCount |-> 0, committed |-> FALSE]),
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> (r1 :> <<[term |-> 2, value |-> v1]>> @@ r2 :> <<>> @@ r3 :> <<>>),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 1,
 messages |-> << >>,
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
],
[
 _TEAction |-> [
   position |-> 3,
   name |-> "Next",
   location |-> "line 567, col 9 to line 581, col 58 of module raft"
 ],
 allLogs |-> {<<>>, <<[term |-> 2, value |-> v1]>>},
 commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> ( <<1, 2>> :> [sentCount |-> 0, ackCount |-> 0, committed |-> FALSE] @@
  <<2, 2>> :> [sentCount |-> 0, ackCount |-> 0, committed |-> FALSE] ),
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> ( r1 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r2 :> <<>> @@
  r3 :> <<>> ),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 2,
 messages |-> << >>,
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
],
[
 _TEAction |-> [
   position |-> 4,
   name |-> "Next",
   location |-> "line 567, col 9 to line 581, col 58 of module raft"
 ],
 allLogs |-> { <<>>,
  <<[term |-> 2, value |-> v1]>>,
  <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> },
 commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> ( <<1, 2>> :> [sentCount |-> 1, ackCount |-> 0, committed |-> FALSE] @@
  <<2, 2>> :> [sentCount |-> 0, ackCount |-> 0, committed |-> FALSE] ),
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> ( r1 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r2 :> <<>> @@
  r3 :> <<>> ),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 2,
 messages |-> ( [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 0 ] :>
      1 ),
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
],
[
 _TEAction |-> [
   position |-> 5,
   name |-> "Next",
   location |-> "line 567, col 9 to line 581, col 58 of module raft"
 ],
 allLogs |-> { <<>>,
  <<[term |-> 2, value |-> v1]>>,
  <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> },
 commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> ( <<1, 2>> :> [sentCount |-> 1, ackCount |-> 0, committed |-> FALSE] @@
  <<2, 2>> :> [sentCount |-> 0, ackCount |-> 0, committed |-> FALSE] ),
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> ( r1 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r2 :> <<[term |-> 2, value |-> v1]>> @@
  r3 :> <<>> ),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 2,
 messages |-> ( [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 0 ] :>
      1 ),
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
],
[
 _TEAction |-> [
   position |-> 6,
   name |-> "Next",
   location |-> "line 567, col 9 to line 581, col 58 of module raft"
 ],
 allLogs |-> { <<>>,
  <<[term |-> 2, value |-> v1]>>,
  <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> },
 commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> ( <<1, 2>> :> [sentCount |-> 1, ackCount |-> 0, committed |-> FALSE] @@
  <<2, 2>> :> [sentCount |-> 0, ackCount |-> 0, committed |-> FALSE] ),
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> ( r1 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r2 :> <<[term |-> 2, value |-> v1]>> @@
  r3 :> <<>> ),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 2,
 messages |-> ( [ mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msource |-> r2,
    mdest |-> r1,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      1 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 0 ] :>
      0 ),
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
],
[
 _TEAction |-> [
   position |-> 7,
   name |-> "Next",
   location |-> "line 567, col 9 to line 581, col 58 of module raft"
 ],
 allLogs |-> { <<>>,
  <<[term |-> 2, value |-> v1]>>,
  <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> },
 commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> ( <<1, 2>> :> [sentCount |-> 1, ackCount |-> 1, committed |-> FALSE] @@
  <<2, 2>> :> [sentCount |-> 0, ackCount |-> 0, committed |-> FALSE] ),
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> ( r1 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r2 :> <<[term |-> 2, value |-> v1]>> @@
  r3 :> <<>> ),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 2,
 messages |-> ( [ mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msource |-> r2,
    mdest |-> r1,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 0 ] :>
      0 ),
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
],
[
 _TEAction |-> [
   position |-> 8,
   name |-> "Next",
   location |-> "line 567, col 9 to line 581, col 58 of module raft"
 ],
 allLogs |-> { <<>>,
  <<[term |-> 2, value |-> v1]>>,
  <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> },
 commitIndex |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> ( <<1, 2>> :> [sentCount |-> 1, ackCount |-> 1, committed |-> TRUE] @@
  <<2, 2>> :> [sentCount |-> 0, ackCount |-> 0, committed |-> FALSE] ),
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> ( r1 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r2 :> <<[term |-> 2, value |-> v1]>> @@
  r3 :> <<>> ),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 2,
 messages |-> ( [ mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msource |-> r2,
    mdest |-> r1,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 0 ] :>
      0 ),
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
],
[
 _TEAction |-> [
   position |-> 9,
   name |-> "Next",
   location |-> "line 567, col 9 to line 581, col 58 of module raft"
 ],
 allLogs |-> { <<>>,
  <<[term |-> 2, value |-> v1]>>,
  <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> },
 commitIndex |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> ( <<1, 2>> :> [sentCount |-> 1, ackCount |-> 1, committed |-> TRUE] @@
  <<2, 2>> :> [sentCount |-> 1, ackCount |-> 0, committed |-> FALSE] ),
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> ( r1 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r2 :> <<[term |-> 2, value |-> v1]>> @@
  r3 :> <<>> ),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 2,
 messages |-> ( [ mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msource |-> r2,
    mdest |-> r1,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> v2]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 1 ] :>
      1 ),
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
],
[
 _TEAction |-> [
   position |-> 10,
   name |-> "Next",
   location |-> "line 567, col 9 to line 581, col 58 of module raft"
 ],
 allLogs |-> { <<>>,
  <<[term |-> 2, value |-> v1]>>,
  <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> },
 commitIndex |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> ( <<1, 2>> :> [sentCount |-> 1, ackCount |-> 1, committed |-> TRUE] @@
  <<2, 2>> :> [sentCount |-> 1, ackCount |-> 0, committed |-> FALSE] ),
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> ( r1 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r2 :> <<[term |-> 2, value |-> v1]>> @@
  r3 :> <<>> ),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 2,
 messages |-> ( [ mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msource |-> r2,
    mdest |-> r1,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> v2]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 1 ] :>
      1 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r3,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 1 ] :>
      1 ),
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
],
[
 _TEAction |-> [
   position |-> 11,
   name |-> "Next",
   location |-> "line 567, col 9 to line 581, col 58 of module raft"
 ],
 allLogs |-> { <<>>,
  <<[term |-> 2, value |-> v1]>>,
  <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> },
 commitIndex |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> ( <<1, 2>> :> [sentCount |-> 1, ackCount |-> 1, committed |-> TRUE] @@
  <<2, 2>> :> [sentCount |-> 1, ackCount |-> 0, committed |-> FALSE] ),
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> ( r1 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r2 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r3 :> <<>> ),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 2,
 messages |-> ( [ mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msource |-> r2,
    mdest |-> r1,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> v2]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 1 ] :>
      1 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r3,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 1 ] :>
      1 ),
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
],
[
 _TEAction |-> [
   position |-> 12,
   name |-> "Next",
   location |-> "line 567, col 9 to line 581, col 58 of module raft"
 ],
 allLogs |-> { <<>>,
  <<[term |-> 2, value |-> v1]>>,
  <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> },
 commitIndex |-> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 0),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> ( <<1, 2>> :> [sentCount |-> 1, ackCount |-> 1, committed |-> TRUE] @@
  <<2, 2>> :> [sentCount |-> 1, ackCount |-> 0, committed |-> FALSE] ),
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> ( r1 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r2 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r3 :> <<>> ),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 2,
 messages |-> ( [ mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msource |-> r2,
    mdest |-> r1,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msource |-> r2,
    mdest |-> r1,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      1 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> v2]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r3,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 1 ] :>
      1 ),
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
],
[
 _TEAction |-> [
   position |-> 13,
   name |-> "Next",
   location |-> "line 567, col 9 to line 581, col 58 of module raft"
 ],
 allLogs |-> { <<>>,
  <<[term |-> 2, value |-> v1]>>,
  <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> },
 commitIndex |-> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 0),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> ( <<1, 2>> :> [sentCount |-> 1, ackCount |-> 1, committed |-> TRUE] @@
  <<2, 2>> :> [sentCount |-> 1, ackCount |-> 0, committed |-> FALSE] ),
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> ( r1 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r2 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r3 :> <<[term |-> 2, value |-> v1]>> ),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 2,
 messages |-> ( [ mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msource |-> r2,
    mdest |-> r1,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msource |-> r2,
    mdest |-> r1,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      1 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> v2]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r3,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 1 ] :>
      1 ),
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
],
[
 _TEAction |-> [
   position |-> 14,
   name |-> "Next",
   location |-> "line 567, col 9 to line 581, col 58 of module raft"
 ],
 allLogs |-> { <<>>,
  <<[term |-> 2, value |-> v1]>>,
  <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> },
 commitIndex |-> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1),
 currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),
 elections |-> { [ eterm |-> 2,
    eleader |-> r1,
    elog |-> <<>>,
    evotes |-> {r1},
    evoterLog |-> (r1 :> <<>>) ] },
 entryCommitStats |-> ( <<1, 2>> :> [sentCount |-> 1, ackCount |-> 1, committed |-> TRUE] @@
  <<2, 2>> :> [sentCount |-> 1, ackCount |-> 0, committed |-> FALSE] ),
 leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),
 log |-> ( r1 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r2 :> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>> @@
  r3 :> <<[term |-> 2, value |-> v1]>> ),
 matchIndex |-> ( r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@
  r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
  r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) ),
 maxc |-> 2,
 messages |-> ( [ mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msource |-> r2,
    mdest |-> r1,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msource |-> r2,
    mdest |-> r1,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      1 @@
  [ mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msource |-> r3,
    mdest |-> r1,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      1 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r2,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> v2]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    msource |-> r1,
    mdest |-> r3,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> v1]>>,
    mlog |-> <<[term |-> 2, value |-> v1], [term |-> 2, value |-> v2]>>,
    mcommitIndex |-> 1 ] :>
      0 ),
 nextIndex |-> ( r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@
  r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
  r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) ),
 state |-> (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower),
 votedFor |-> (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1),
 voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),
 votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),
 votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
]
>>