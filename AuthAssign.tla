------ MODULE AuthAssign ----
EXTENDS TLC, Naturals

CONSTANT User, nil

VARIABLES db_assign, handle_status,
    want_assign, want_changes,
    disk_assign,
    pc, local_wanted, local_user, num_downtime

max_want_changes == 5

max_down_times == 2

NullUser == User \union {nil}

want_vars == <<want_assign, want_changes>>
job_vars == <<handle_status, pc, local_wanted, local_user, num_downtime>>

vars == <<db_assign, want_vars, disk_assign, job_vars>>


DBStatus == {"null", "handling", "added"}

HandleStatus == {"null", "processing"}

DiskStatus == {"active", "null"}

TypeOK ==
    /\ db_assign \in [User -> DBStatus]
    /\ handle_status \in [User -> HandleStatus]
    /\ want_assign \subseteq User
    /\ want_changes \in 0..max_want_changes
    /\ disk_assign \in [User -> DiskStatus]
    /\ pc \in {"Init", "ReadDB", "AssignPerm", "RemovePerm", "UpdateDB"}
    /\ local_wanted \in BOOLEAN
    /\ local_user \in NullUser
    /\ num_downtime \in 0..max_down_times


Init == 
    /\ db_assign = [u \in User |-> "null"]
    /\ handle_status = [u \in User |-> "null"]
    /\ want_assign = {}
    /\ want_changes = 0
    /\ disk_assign = [u \in User |-> "null"]
    /\ pc = "Init"
    /\ local_wanted = FALSE
    /\ local_user = nil
    /\ num_downtime = 0


incWantChanges ==
    /\ want_changes < max_want_changes
    /\ want_changes' = want_changes + 1

AddWanted(u) ==
    /\ ~(u \in want_assign)
    /\ incWantChanges
    /\ want_assign' = want_assign \union {u}
    /\ UNCHANGED <<db_assign, disk_assign>>
    /\ UNCHANGED job_vars


RemoveWanted(u) ==
    /\ u \in want_assign
    /\ incWantChanges
    /\ want_assign' = want_assign \ {u}
    /\ UNCHANGED <<db_assign, disk_assign>>
    /\ UNCHANGED job_vars


noDifferenceForUser(u) ==
    IF u \in want_assign
        THEN db_assign[u] = "added"
        ELSE db_assign[u] = "null"


noDifferenceBetweenWantedAndDB ==
    \A u \in User: noDifferenceForUser(u)


GetFromWanted(u) ==
    /\ pc = "Init"
    /\ \/ ~noDifferenceForUser(u) \* enable if there is a difference
       \/ handle_status[u] = "processing"
    /\ pc' = "ReadDB"
    /\ local_user' = u
    /\ local_wanted' = (u \in want_assign)
    /\ UNCHANGED num_downtime
    /\ UNCHANGED want_vars
    /\ UNCHANGED <<db_assign, handle_status>>
    /\ UNCHANGED disk_assign


resetToInit ==
    /\ pc' = "Init"
    /\ local_user' = nil
    /\ local_wanted' = FALSE



setHandleProcessing ==
    /\ handle_status' = [handle_status EXCEPT ![local_user] = "processing"]


getFromDBHandleWanted ==
    IF db_assign[local_user] = "null" \/ handle_status[local_user] = "processing"
        THEN
            /\ pc' = "AssignPerm"
            /\ setHandleProcessing
            /\ UNCHANGED <<local_user, local_wanted>>
        ELSE
            /\ resetToInit
            /\ UNCHANGED handle_status


getFromDBHandleNotWanted ==
    IF db_assign[local_user] = "added" \/ handle_status[local_user] = "processing"
        THEN
            /\ pc' = "RemovePerm"
            /\ setHandleProcessing
            /\ UNCHANGED <<local_user, local_wanted>>
        ELSE
            /\ resetToInit
            /\ UNCHANGED handle_status


GetFromDB ==
    /\ pc = "ReadDB"
    /\ IF local_wanted
        THEN getFromDBHandleWanted
        ELSE getFromDBHandleNotWanted
    /\ UNCHANGED num_downtime
    /\ UNCHANGED want_vars
    /\ UNCHANGED db_assign
    /\ UNCHANGED disk_assign


AssignPerm ==
    /\ pc = "AssignPerm"
    /\ pc' = "UpdateDB"
    /\ disk_assign' = [disk_assign EXCEPT ![local_user] = "active"]
    /\ UNCHANGED <<local_user, local_wanted>>
    /\ UNCHANGED num_downtime
    /\ UNCHANGED want_vars
    /\ UNCHANGED <<db_assign, handle_status>>


RemovePerm ==
    /\ pc = "RemovePerm"
    /\ pc' = "UpdateDB"
    /\ disk_assign' = [disk_assign EXCEPT ![local_user] = "null"] \* delete
    /\ UNCHANGED <<local_user, local_wanted>>
    /\ UNCHANGED num_downtime
    /\ UNCHANGED want_vars
    /\ UNCHANGED <<db_assign, handle_status>>


UpdateDB ==
    /\ pc = "UpdateDB"
    /\ IF local_wanted
        THEN db_assign' = [db_assign EXCEPT ![local_user] = "added"]
        ELSE db_assign' = [db_assign EXCEPT ![local_user] = "null"]
    /\ resetToInit
    /\ handle_status' = [handle_status EXCEPT ![local_user] = "null"]
    /\ UNCHANGED num_downtime
    /\ UNCHANGED disk_assign
    /\ UNCHANGED want_vars


DownTime ==
    /\ num_downtime < max_down_times
    /\ num_downtime' = num_downtime + 1
    /\ pc # "Init"
    /\ resetToInit
    /\ UNCHANGED <<want_assign, db_assign, handle_status, disk_assign>>
    /\ UNCHANGED want_changes


TerminateCond ==
    /\ want_changes = max_want_changes
    /\ pc = "Init"
    /\ noDifferenceBetweenWantedAndDB
    /\ \A u \in User: handle_status[u] = "null"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

Next ==
    \/ \E u \in User:
        \/ AddWanted(u)
        \/ RemoveWanted(u)
        \/ GetFromWanted(u)
    \/ GetFromDB
    \/ AssignPerm
    \/ RemovePerm
    \/ UpdateDB
    \/ DownTime
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)


AlwaysTerminate == <> TerminateCond


ResetFully ==
    pc = "Init" =>
        /\ local_user = nil
        /\ local_wanted = FALSE
    

noDifferenceBetweenWantedAndDisk(u) ==
    IF u \in want_assign
        THEN disk_assign[u] = "active"
        ELSE disk_assign[u] = "null"

Inv ==
    TerminateCond =>
        /\ \A u \in User: noDifferenceBetweenWantedAndDisk(u)

====