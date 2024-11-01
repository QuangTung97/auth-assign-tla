------ MODULE AuthAssign ----
EXTENDS TLC

CONSTANT User

VARIABLES db_assign, disk_assign

vars == <<db_assign, disk_assign>>

DBStatus == {"null"}

DiskStatus == {"active", "null"}

TypeOK ==
    /\ db_assign \in [User -> DBStatus]
    /\ disk_assign \in [User -> DiskStatus]


Init == 
    /\ db_assign = [u \in User |-> "null"]
    /\ disk_assign = [u \in User |-> "null"]


TerminateCond ==
    /\ TRUE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

Next ==
    \/ Terminated

====