---- MODULE TPC ----
EXTENDS TwoPhaseCommit, TLC

\* CONSTANT definitions @modelParameterConstants:0RM
rm_const == 
{1, 2, 3}
----

\* CONSTANT definitions @modelParameterConstants:1N
n_const == 
3
----

=============================================================================