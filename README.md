
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
