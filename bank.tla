---- MODULE bank ----
EXTENDS Integers

CONSTANTS Customers

VARIABLES state, balance

Init ==
    /\ state = [c \in Customers |-> "open"]
    /\ balance = [c \in Customers |-> 0]

Deposit(customer, amount) ==
    /\ state[customer] = "open"
    /\ balance[customer] < 100
    /\ balance' = [balance EXCEPT![customer] = (balance[customer] + amount)]
    /\ UNCHANGED <<state>>

Withdraw(customer, amount) ==
    /\ state[customer] = "open"
    /\ (balance[customer] - amount) >= 0
    /\ balance' = [balance EXCEPT![customer] = (balance[customer] - amount)]
    /\ UNCHANGED <<state>>

Close(customer) ==
    /\ state[customer] = "open"
    /\ state' = [state EXCEPT![customer] = "closed"]
    /\ UNCHANGED <<balance>>

Reopen(customer) ==
    /\ state[customer] = "closed"
    /\ state' = [state EXCEPT![customer] = "open"]
    /\ UNCHANGED <<balance>>

Transfer(from, to, amount) ==
    /\ from # to
    /\ Withdraw(from, amount)
    /\ Deposit(to, amount)

Next ==
    \/ \E from \in Customers, amount \in 1..10:
        Deposit(from, amount)
    \/ \E from \in Customers, amount \in 1..10:
        Withdraw(from, amount)
    \/ \E from \in Customers:
        Close(from)
    \/ \E from \in Customers:
        Reopen(from)
    \/ \E from, to \in Customers, amount \in 1..10:
        Transfer(from, to, amount)

Spec == Init /\ [][Next]_state

NoNegativeBalance ==
    /\ \A customer \in Customers:
        balance[customer] >= 0
====
