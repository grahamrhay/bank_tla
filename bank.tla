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

Next ==
    /\ \E customer \in Customers:
        \/ \E amount \in 1..10:
                Deposit(customer, amount)
        \/ \E amount \in 1..10:
                Withdraw(customer, amount)
        \/ Close(customer)
        \/ Reopen(customer)

Spec == Init /\ [][Next]_state

NoNegativeBalance ==
    /\ \A customer \in Customers:
        balance[customer] >= 0
====
