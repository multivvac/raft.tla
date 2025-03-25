
Formal TLA+ specification for the [Raft consensus algorithm](https://raftconsensus.github.io). This is slightly updated compared to the dissertation version.

For more information, see Chapter 8 (Correctness) and Appendix B (Safety proof and formal specification) in https://github.com/ongardie/dissertation .

If you're trying to run the TLA+ model checker on this specification, check out Jin Li's changes in [Pull Request #4](https://github.com/ongardie/raft.tla/pull/4/).

Copyright 2014 Diego Ongaro.

This work is licensed under the Creative Commons Attribution-4.0 International License https://creativecommons.org/licenses/by/4.0/ .

Modified by Ovidiu Marcu

How to run?

1)
You can run one configuration see raft.cfg with: `./tlc.py -n --trace-name Terr1 --dot --coverage 1 mc raft.tla`, at latest commit.

OR 

2)
check the following with the Toolbox:

git checkout b7dffa9045541acd73568ee0a161ea60d919e298

State constraint for model checking

(\A i \in Server: currentTerm[i] <= 3 /\ Len(log[i]) <= 3 ) /\ (\A m \in DOMAIN messages: messages[m] <= 1)

Disable Profiling in TLC Options. See screenshots for initializing model and expected results.

TLC command line parameters: -coverage 1
My model

---- MODULE MC ----
EXTENDS raft, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Server
const_1742894465167335000 == 
{r1, r2, r3}
----

\* MV CONSTANT definitions Value
const_1742894465167336000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_1742894465167337000 == 
Permutations(const_1742894465167335000)
----

\* CONSTANT definitions @modelParameterConstants:10MaxClientRequests
const_1742894465167338000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:11MaxBecomeLeader
const_1742894465167339000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:12MaxTerm
const_1742894465167340000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1742894465168341000 ==
(\A i \in Server: currentTerm[i] <= 3 /\ Len(log[i]) <= 3 ) /\ (\A m \in DOMAIN messages: messages[m] <= 1)
----
=============================================================================
\* Modification History
\* Created Tue Mar 25 10:21:05 CET 2025 by ovidiu-cristian.marcu
