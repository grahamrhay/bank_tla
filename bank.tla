---- MODULE bank ----
EXTENDS Integers, FiniteSets

CONSTANTS Customers

VARIABLES state, balance, transfers

Init ==
    /\ state = [c \in Customers |-> "open"]
    /\ balance = [c \in Customers |-> 0]
    /\ transfers = {}

Deposit(customer, amount) ==
    /\ state[customer] = "open"
    /\ balance[customer] < 10
    /\ balance' = [balance EXCEPT![customer] = (balance[customer] + amount)]
    /\ UNCHANGED <<state, transfers>>

Withdraw(customer, amount) ==
    /\ state[customer] = "open"
    /\ (balance[customer] - amount) >= 0
    /\ balance' = [balance EXCEPT![customer] = (balance[customer] - amount)]
    /\ UNCHANGED <<state, transfers>>

Close(customer) ==
    /\ state[customer] = "open"
    /\ state' = [state EXCEPT![customer] = "closed"]
    /\ UNCHANGED <<balance, transfers>>

Reopen(customer) ==
    /\ state[customer] = "closed"
    /\ state' = [state EXCEPT![customer] = "open"]
    /\ UNCHANGED <<balance, transfers>>

Transfer(from, to, amount) ==
    /\ Cardinality(transfers) < 1
    /\ from # to
    /\ state[from] = "open"
    /\ state[to] = "open"
    /\ (balance[from] - amount) >= 0
    /\ transfers' = transfers \union { [ from |-> from, to |-> to, amount |-> amount ] }
    /\ UNCHANGED <<balance, state>>

Complete(transfer) ==
    /\ transfers' = transfers \ { transfer }
    /\ balance' = [balance EXCEPT![transfer.from] = (balance[transfer.from] - transfer.amount), ![transfer.to] = (balance[transfer.to] + transfer.amount)]
    /\ UNCHANGED <<state>>

Next ==
    /\ \E from, to \in Customers, amount \in 1..10:
        \/ Transfer(from, to, amount)
        \/ Deposit(from, amount)
        \/ Withdraw(from, amount)
        \/ Close(from)
        \/ Reopen(from)
        \/ \E t \in transfers:
            Complete(t)

Spec == Init /\ [][Next]_state

NoNegativeBalance ==
    /\ \A customer \in Customers:
        balance[customer] >= 0
====
