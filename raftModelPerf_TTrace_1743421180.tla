---- MODULE raftModelPerf_TTrace_1743421180 ----
EXTENDS Sequences, raftModelPerf, TLCExt, raftModelPerf_TEConstants, Toolbox, Naturals, TLC

_expression ==
    LET raftModelPerf_TEExpression == INSTANCE raftModelPerf_TEExpression
    IN raftModelPerf_TEExpression!expression
----

_trace ==
    LET raftModelPerf_TETrace == INSTANCE raftModelPerf_TETrace
    IN raftModelPerf_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        votedFor = ((r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1))
        /\
        log = ((r1 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r2 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r3 :> <<[term |-> 2, value |-> v2]>>))
        /\
        voterLog = ((r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>))
        /\
        nextIndex = ((r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)))
        /\
        maxc = (2)
        /\
        currentTerm = ((r1 :> 2 @@ r2 :> 2 @@ r3 :> 2))
        /\
        entryCommitStats = ((<<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@ <<2, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0]))
        /\
        votesResponded = ((r1 :> {r1} @@ r2 :> {} @@ r3 :> {}))
        /\
        votesGranted = ((r1 :> {r1} @@ r2 :> {} @@ r3 :> {}))
        /\
        messages = (([mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 0 @@ [mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 2] :> 1 @@ [mdest |-> r1, msource |-> r3, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 1 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 0 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 1, mprevLogTerm |-> 2, mentries |-> <<[term |-> 2, value |-> v1]>>, mcommitIndex |-> 1] :> 0 @@ [mdest |-> r3, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 1] :> 0))
        /\
        matchIndex = ((r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)))
        /\
        state = ((r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower))
        /\
        leaderCount = ((r1 :> 1 @@ r2 :> 0 @@ r3 :> 0))
        /\
        commitIndex = ((r1 :> 1 @@ r2 :> 1 @@ r3 :> 1))
    )
----

_init ==
    /\ messages = _TETrace[1].messages
    /\ matchIndex = _TETrace[1].matchIndex
    /\ log = _TETrace[1].log
    /\ state = _TETrace[1].state
    /\ leaderCount = _TETrace[1].leaderCount
    /\ entryCommitStats = _TETrace[1].entryCommitStats
    /\ commitIndex = _TETrace[1].commitIndex
    /\ currentTerm = _TETrace[1].currentTerm
    /\ votesResponded = _TETrace[1].votesResponded
    /\ maxc = _TETrace[1].maxc
    /\ nextIndex = _TETrace[1].nextIndex
    /\ votesGranted = _TETrace[1].votesGranted
    /\ voterLog = _TETrace[1].voterLog
    /\ votedFor = _TETrace[1].votedFor
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ messages  = _TETrace[i].messages
        /\ messages' = _TETrace[j].messages
        /\ matchIndex  = _TETrace[i].matchIndex
        /\ matchIndex' = _TETrace[j].matchIndex
        /\ log  = _TETrace[i].log
        /\ log' = _TETrace[j].log
        /\ state  = _TETrace[i].state
        /\ state' = _TETrace[j].state
        /\ leaderCount  = _TETrace[i].leaderCount
        /\ leaderCount' = _TETrace[j].leaderCount
        /\ entryCommitStats  = _TETrace[i].entryCommitStats
        /\ entryCommitStats' = _TETrace[j].entryCommitStats
        /\ commitIndex  = _TETrace[i].commitIndex
        /\ commitIndex' = _TETrace[j].commitIndex
        /\ currentTerm  = _TETrace[i].currentTerm
        /\ currentTerm' = _TETrace[j].currentTerm
        /\ votesResponded  = _TETrace[i].votesResponded
        /\ votesResponded' = _TETrace[j].votesResponded
        /\ maxc  = _TETrace[i].maxc
        /\ maxc' = _TETrace[j].maxc
        /\ nextIndex  = _TETrace[i].nextIndex
        /\ nextIndex' = _TETrace[j].nextIndex
        /\ votesGranted  = _TETrace[i].votesGranted
        /\ votesGranted' = _TETrace[j].votesGranted
        /\ voterLog  = _TETrace[i].voterLog
        /\ voterLog' = _TETrace[j].voterLog
        /\ votedFor  = _TETrace[i].votedFor
        /\ votedFor' = _TETrace[j].votedFor

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("raftModelPerf_TTrace_1743421180.json", _TETrace)

=============================================================================

 Note that you can extract this module `raftModelPerf_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `raftModelPerf_TEExpression.tla` file takes precedence 
  over the module `raftModelPerf_TEExpression` below).

---- MODULE raftModelPerf_TEExpression ----
EXTENDS Sequences, raftModelPerf, TLCExt, raftModelPerf_TEConstants, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `raftModelPerf` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        messages |-> messages
        ,matchIndex |-> matchIndex
        ,log |-> log
        ,state |-> state
        ,leaderCount |-> leaderCount
        ,entryCommitStats |-> entryCommitStats
        ,commitIndex |-> commitIndex
        ,currentTerm |-> currentTerm
        ,votesResponded |-> votesResponded
        ,maxc |-> maxc
        ,nextIndex |-> nextIndex
        ,votesGranted |-> votesGranted
        ,voterLog |-> voterLog
        ,votedFor |-> votedFor
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_messagesUnchanged |-> messages = messages'
        
        \* Format the `messages` variable as Json value.
        \* ,_messagesJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(messages)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_messagesModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].messages # _TETrace[s-1].messages
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE raftModelPerf_TETrace ----
\*EXTENDS IOUtils, raftModelPerf, raftModelPerf_TEConstants, TLC
\*
\*trace == IODeserialize("raftModelPerf_TTrace_1743421180.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE raftModelPerf_TETrace ----
EXTENDS raftModelPerf, raftModelPerf_TEConstants, TLC

trace == 
    <<
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<>> @@ r2 :> <<>> @@ r3 :> <<>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 0,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> <<>>,votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> <<>>,matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)]),
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<[term |-> 2, value |-> v2]>> @@ r2 :> <<>> @@ r3 :> <<>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 1,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> (<<1, 2>> :> [committed |-> FALSE, sentCount |-> 0, ackCount |-> 0]),votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> <<>>,matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)]),
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<[term |-> 2, value |-> v2]>> @@ r2 :> <<>> @@ r3 :> <<>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 1,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> (<<1, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0]),votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> ([mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 1),matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)]),
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r2 :> <<>> @@ r3 :> <<>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 2,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> (<<1, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] @@ <<2, 2>> :> [committed |-> FALSE, sentCount |-> 0, ackCount |-> 0]),votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> ([mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 1),matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)]),
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r2 :> <<[term |-> 2, value |-> v2]>> @@ r3 :> <<>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 2,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> (<<1, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] @@ <<2, 2>> :> [committed |-> FALSE, sentCount |-> 0, ackCount |-> 0]),votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> ([mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 1),matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)]),
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r2 :> <<[term |-> 2, value |-> v2]>> @@ r3 :> <<>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 2,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> (<<1, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] @@ <<2, 2>> :> [committed |-> FALSE, sentCount |-> 0, ackCount |-> 0]),votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> ([mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 1 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 0),matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)]),
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r2 :> <<[term |-> 2, value |-> v2]>> @@ r3 :> <<>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 2,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> (<<1, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 1] @@ <<2, 2>> :> [committed |-> FALSE, sentCount |-> 0, ackCount |-> 0]),votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> ([mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 0 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 0),matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)]),
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r2 :> <<[term |-> 2, value |-> v2]>> @@ r3 :> <<>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 2,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> (<<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@ <<2, 2>> :> [committed |-> FALSE, sentCount |-> 0, ackCount |-> 0]),votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> ([mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 0 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 0),matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0)]),
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r2 :> <<[term |-> 2, value |-> v2]>> @@ r3 :> <<>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 2,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> (<<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@ <<2, 2>> :> [committed |-> FALSE, sentCount |-> 0, ackCount |-> 0]),votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> ([mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 0 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 0 @@ [mdest |-> r3, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 1] :> 1),matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0)]),
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r2 :> <<[term |-> 2, value |-> v2]>> @@ r3 :> <<>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 2,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> (<<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@ <<2, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0]),votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> ([mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 0 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 0 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 1, mprevLogTerm |-> 2, mentries |-> <<[term |-> 2, value |-> v1]>>, mcommitIndex |-> 1] :> 1 @@ [mdest |-> r3, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 1] :> 1),matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0)]),
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r2 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r3 :> <<>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 2,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> (<<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@ <<2, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0]),votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> ([mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 0 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 0 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 1, mprevLogTerm |-> 2, mentries |-> <<[term |-> 2, value |-> v1]>>, mcommitIndex |-> 1] :> 1 @@ [mdest |-> r3, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 1] :> 1),matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0)]),
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r2 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r3 :> <<>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 2,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> (<<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@ <<2, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0]),votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> ([mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 0 @@ [mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 2] :> 1 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 0 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 1, mprevLogTerm |-> 2, mentries |-> <<[term |-> 2, value |-> v1]>>, mcommitIndex |-> 1] :> 0 @@ [mdest |-> r3, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 1] :> 1),matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 0)]),
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r2 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r3 :> <<[term |-> 2, value |-> v2]>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 2,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> (<<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@ <<2, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0]),votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> ([mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 0 @@ [mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 2] :> 1 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 0 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 1, mprevLogTerm |-> 2, mentries |-> <<[term |-> 2, value |-> v1]>>, mcommitIndex |-> 1] :> 0 @@ [mdest |-> r3, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 1] :> 1),matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 0)]),
    ([votedFor |-> (r1 :> M_Nil @@ r2 :> r1 @@ r3 :> r1),log |-> (r1 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r2 :> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>> @@ r3 :> <<[term |-> 2, value |-> v2]>>),voterLog |-> (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>),nextIndex |-> (r1 :> (r1 :> 1 @@ r2 :> 2 @@ r3 :> 1) @@ r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@ r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)),maxc |-> 2,currentTerm |-> (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2),entryCommitStats |-> (<<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@ <<2, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0]),votesResponded |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),votesGranted |-> (r1 :> {r1} @@ r2 :> {} @@ r3 :> {}),messages |-> ([mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 0 @@ [mdest |-> r1, msource |-> r2, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 2] :> 1 @@ [mdest |-> r1, msource |-> r3, mtype |-> M_AppendEntriesResponse, mterm |-> 2, msuccess |-> TRUE, mmatchIndex |-> 1] :> 1 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 0] :> 0 @@ [mdest |-> r2, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 1, mprevLogTerm |-> 2, mentries |-> <<[term |-> 2, value |-> v1]>>, mcommitIndex |-> 1] :> 0 @@ [mdest |-> r3, msource |-> r1, mtype |-> M_AppendEntriesRequest, mterm |-> 2, mlog |-> <<[term |-> 2, value |-> v2], [term |-> 2, value |-> v1]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, mentries |-> <<[term |-> 2, value |-> v2]>>, mcommitIndex |-> 1] :> 0),matchIndex |-> (r1 :> (r1 :> 0 @@ r2 :> 1 @@ r3 :> 0) @@ r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@ r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)),state |-> (r1 :> M_Leader @@ r2 :> M_Follower @@ r3 :> M_Follower),leaderCount |-> (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0),commitIndex |-> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1)])
    >>
----


=============================================================================

---- MODULE raftModelPerf_TEConstants ----
EXTENDS raftModelPerf

CONSTANTS M_Follower, M_Candidate, M_Leader, M_Nil, M_RequestVoteRequest, M_RequestVoteResponse, M_AppendEntriesRequest, M_AppendEntriesResponse, v1, v2, r1, r2, r3

=============================================================================

---- CONFIG raftModelPerf_TTrace_1743421180 ----
CONSTANTS
    Follower = M_Follower
    Candidate = M_Candidate
    Leader = M_Leader
    Nil = M_Nil
    RequestVoteRequest = M_RequestVoteRequest
    RequestVoteResponse = M_RequestVoteResponse
    AppendEntriesRequest = M_AppendEntriesRequest
    AppendEntriesResponse = M_AppendEntriesResponse
    MaxClientRequests = 2
    MaxBecomeLeader = 1
    MaxTerm = 2
    Value = { v1 , v2 }
    Server = { r1 , r2 , r3 }
    M_AppendEntriesRequest = M_AppendEntriesRequest
    M_Nil = M_Nil
    M_Candidate = M_Candidate
    M_Follower = M_Follower
    r3 = r3
    r1 = r1
    M_AppendEntriesResponse = M_AppendEntriesResponse
    M_RequestVoteResponse = M_RequestVoteResponse
    M_RequestVoteRequest = M_RequestVoteRequest
    M_Leader = M_Leader
    r2 = r2
    v2 = v2
    v1 = v1

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Mon Mar 31 13:39:43 CEST 2025