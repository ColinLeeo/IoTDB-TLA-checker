(*
倒水问题：
初始一个 3L与一个 5L的水桶，问如何倒水使得其中一个水桶中有4L的水
*) 

------------------------------- MODULE DieHard -------------------------------
EXTENDS Integers 

VARIABLES big, small

Init == big = 0 /\ small = 0
TypeOk == small \in 0..3 /\ big \in 0..5

FillSmall == small' = 3 /\ big' = big
FillBig == big' = 5 /\ small' = small
EmptySmall == small' = 0 /\ big' = big
EmptyBig == big' = 0 /\ small' = small

Min(m,n) == IF m < n THEN m ELSE n 

SmallToBig == big' = Min(5, big + small)
                /\ small' =  small - (big' - big)

BigToSmall == small' = Min(3, big + small)
                /\ big' = big - (small' - small)

Next == \/ FillSmall
       \/ FillBig
       \/ EmptySmall
       \/ EmptyBig
       \/ BigToSmall
       \/ SmallToBig

Check == TypeOk /\ big /= 4

=============================================================================