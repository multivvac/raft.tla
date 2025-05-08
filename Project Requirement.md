# Project Description

Inspired from the HovercRaft paper, and using the Raft spec modified with the third exercise, 

here are the requirements and changes HovercRaft introduces compared to standard Raft, 

aiming for scalability while preserving Raft's core safety and liveness - see attached the design.

You will have to design the Switch component as follows.


Adding the Switch component:

Clients must send requests via a Switch mechanism (like IP Multicast or a middlebox replicating requests) 

that delivers the request payload to all server nodes (leader and followers) simultaneously.

```
client -> multiple clientreq -> switch -> server
HandleAppendEntriesReq match metadata handle with ordered data
HandleAppendEntriesResponse not reply to switch

dropmessage for bonus recover test

client request handle?s
```

Requirement: The leader node is only responsible for ordering requests by sending fixed-size metadata messages 

(referencing the client request) to followers, not the full request payload. You should separate the payload from client requests.


Requirement: Followers must temporarily store unordered client requests received via Switch multicast and match them 

with the ordering metadata received from the leader.


Bonus Requirement: A recovery mechanism (recovery_request message) must exist for followers to fetch 

missing client requests (due to unreliable multicast) from the leader or other followers.

Note April 25:

Notes on design on how you enter a client request into the system

entry == [term |-> entryTerm, value |-> v] - represents metadata

term comes from leader, entryTerm == currentTerm[i], where i is the Leader
value is some index from the Value set

entryWithPayload == [term |-> entryTerm, value |-> v, payload |-> v] - this is what goes from Switch to the other Servers

from Leader to Followers we only send the metadata [term |-> entryTerm, value |-> v]

SwitchClientRequest

where

Switch is a fourth Server - switchIndex variable to initialize in MyInit

switchIndex should be initialized in MyInit

SwitchClientRequest

you have to use entryWithPayload and update the log[switchIndex]