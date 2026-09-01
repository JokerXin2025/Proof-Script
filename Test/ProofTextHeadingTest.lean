import ProofScript

@text "==== Level 4"

/--
error: invalid heading or heading label; labels must match [A-Za-z][A-Za-z0-9_-]*
-/
#guard_msgs (error) in
@text "===== Level 5"

/--
error: invalid heading or heading label; labels must match [A-Za-z][A-Za-z0-9_-]*
-/
#guard_msgs (error) in
@text "====== Level 6"
