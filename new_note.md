ddl: last week beginning of this week.
modified myinit.tla
---------raftVariable.tla
should not replicate in 1 atomic step when from switch to server

2nd exercise:
new spec raftModelPerf++
- leader send 1 message to netAgg, from leader to netagg 1 action.
- from netAgg replicate to all follower.
- follower reply back to all the follower.
- netAgg basically just 1 component server act
- netAgg behave like Leader

3nd exercise:
express liveness property about hovercaft++ consider innetwork agg crush

June. 16th Presentation, wrap up all exercise. 5-7mins. 