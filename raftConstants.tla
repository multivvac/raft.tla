--------------------------- MODULE raftConstants ---------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of client requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

\* for instrumentation to limit model state space
CONSTANTS MaxClientRequests

\* Maximum times a server can become a leader
CONSTANTS MaxBecomeLeader

\* Maximum term number allowed in the model
CONSTANTS MaxTerm

\*---------------------------------------------------------------------------
\*  New message kinds                                                         
\*---------------------------------------------------------------------------
CONSTANTS ClientPayload,     \* client -> server, carries large request value
          RecoveryRequest,   \* follower -> any, ask for <<idx,term>> payload
          RecoveryResponse   \* peer -> follower, ships missing payload

=============================================================================
\* Created by Ovidiu-Cristian Marcu
