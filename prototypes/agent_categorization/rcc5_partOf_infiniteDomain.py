from z3 import *

Set = DeclareSort('Set')

X = Const('X', Set)
Y = Const('Y', Set)
Z = Const('Z', Set)

P  = Function('P', Set, Set, BoolSort())
O  = Function('O', Set, Set, BoolSort())
EQ = Function('EQ', Set, Set, BoolSort())
DR = Function('DR', Set, Set, BoolSort())
PO = Function('PO', Set, Set, BoolSort())
PP = Function('PP', Set, Set, BoolSort())
PPi= Function('PPi', Set, Set, BoolSort())


################################
# PART OF
################################

reflexivity=ForAll(X, P(X,X))
antisymmetry=ForAll([X,Y], Implies(And(P(X,Y),P(Y,X)), X==Y))
transitivity=ForAll([X,Y,Z], Implies(And(P(X,Y),P(Y,Z)), P(X,Z))) 

################################
# OVERLAPS 
# O(X,Y) : exists Z P(Z, X) /\ P(Z, Y) 
################################

overlaps=ForAll([X,Y], O(X,Y) == Exists(Z, And(P(Z,X), P(Z,Y))))

################################
# EQUAL TO 
# EQ(X,Y) : P(X, Y ) /\ P(Y, X ) 
################################

equal_to=ForAll([X,Y], EQ(X,Y) == And(P(X,Y), P(Y,X)))

################################
# DISCRETE FROM
# DR(X,Y) : not O(X,Y)
################################

discrete_from=ForAll([X,Y], DR(X,Y) == Not(O(X,Y)))

################################
# PARTIAL OVERLAP
# PO(X,Y) : O(X, Y) /\ (not P(X, Y)) /\ (not P(Y, X))
################################

partial_overlap=ForAll([X,Y], PO(X,Y) == And(O(X,Y), Not(P(X,Y)), Not(P(Y,X))))

################################
# PROPER PART OF 
# PP(X,Y) : P(X, Y) /\ (not P(Y, X)) 
################################

proper_part=ForAll([X,Y], PP(X,Y) == And(P(X,Y), Not(P(Y,X))))

################################
# INVERSE OF PROPER PART OF 
# PPi(X,Y) : P(Y, X) /\ (not P(X, Y)) 
################################

proper_part_i=ForAll([X,Y], PPi(X,Y) == And(P(Y,X), Not(P(X,Y))))

################################
# AGENT
################################

s = Solver()
s.set(auto_config=False, mbqi=False)
s.add(And(reflexivity, antisymmetry, transitivity, proper_part, proper_part_i, partial_overlap, discrete_from, equal_to, overlaps))


A = Const('A', Set)
B = Const('B', Set)
F = Const('F', Set)

rcc5={'eq':EQ, 'pp':PP, 'ppi':PPi, 'po':PO, 'dr':DR}

counter=1
counter_sat=0
counter_unsat=0
counter_unknown=0

for i in rcc5:
    r1=rcc5[i](A,B)
    for j in rcc5:
        r2=rcc5[j](B,F)
        for k in rcc5:
            r3=rcc5[k](A,F)

            agent=And(r1,r2,r3)

            s.push()
            s.add(agent)
            check=s.check()
            offset1=' '*(5-len(str(counter)))
            offset2=' '*(12-len(str(check)))
            print("%d %s %s %s %s"%(counter, offset1, check, offset2, agent))

            if(check == unsat):
                counter_unsat+=1
                #print("a %s"%s.unsat_core())
            if(check == unknown):
                counter_unknown+=1
            if(check == sat):
                counter_sat+=1

            s.pop()
            counter+=1

print("\n********\nSTATISTICS\n\nagents=%d\nsat=%d\nunsat=%d\nunknown=%d"%(counter-1,counter_sat,counter_unsat,counter_unknown))

print("\n")
s.add(ForAll([A,B,F], And(EQ(A,B),EQ(B,F),EQ(A,F))))
print(s.check())
print(s.unsat_core())
