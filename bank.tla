---- MODULE bank ----
EXTENDS Integers

VARIABLES state, balance

Init ==
    /\ state = "open"
    /\ balance = 0

Deposit(amount) ==
    /\ state = "open"
    /\ balance < 100
    /\ balance' = balance + amount
    /\ UNCHANGED <<state>>

Withdraw(amount) ==
    /\ state = "open"
    /\ (balance - amount) >= 0
    /\ balance' = balance - amount
    /\ UNCHANGED <<state>>

Close ==
    /\ state = "open"
    /\ state' = "closed"
    /\ UNCHANGED <<balance>>

Reopen ==
    /\ state = "closed"
    /\ state' = "open"
    /\ UNCHANGED <<balance>>

Next ==
    \/ \E amount \in 1..10:
            Deposit(amount)
    \/ \E amount \in 1..10:
            Withdraw(amount)
    \/ Close
    \/ Reopen

Spec == Init /\ [][Next]_state

NoNegativeBalance ==
    balance >= 0
====
