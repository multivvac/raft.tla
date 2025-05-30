# HovercRaft

## Data-paths
  * Added `SwitchMulticast`, `ReceiveClientPayload`, `RequestRecovery/HandleRecovery*` actions.  
  * Introduced per-node buffers `payloadBuf` and `missingPayload` for unordered payloads.

## Original Raft logic changes
  * `ClientRequest` on the leader now logs *metadata only*; payload is fanned-out once via the Switch.
  * Followers accept an `AppendEntriesRequest` only if `HasPayload` holds; otherwise they stash metadata and later fetch the payload with a recovery RPC.

## Spec mechanics
  * All new variables initialised in `HoverInit`; combined step relation `HoverNext = MysNext \/`.

## Proof / model-checking
  * Strengthened safety invariant `HoverLogInv` to include `HasPayload`. 