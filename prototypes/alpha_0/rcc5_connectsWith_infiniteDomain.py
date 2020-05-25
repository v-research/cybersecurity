from z3 import *

Region = DeclareSort('Region')

X = Const('X', Region)
Y = Const('Y', Region)
Z = Const('Z', Region)

C  = Function('C', Region, Region, BoolSort())
P  = Function('P', Region, Region, BoolSort())
O  = Function('O', Region, Region, BoolSort())
EQ = Function('EQ', Region, Region, BoolSort())
DR = Function('DR', Region, Region, BoolSort())
PO = Function('PO', Region, Region, BoolSort())
PP = Function('PP', Region, Region, BoolSort())
PPi= Function('PPi', Region, Region, BoolSort())

################################
# CONNECTS WITH
# define here the parthood relation C (primitive binary inclusion relation called connects with)  
# which is reflexive and antisymmetric 
################################

reflexivity=ForAll(X, C(X, X))
symmetry=ForAll([X,Y], Implies(C(X, Y), C(Y,X)) )
#extensionality= ForAll([X,Y], Implies(ForAll(Z, C(Z, X) == C(Z, Y)), X == Y))

################################
# PART OF
# P(X,Y) : forall Z C(Z,X) => C(Z,Y)
################################

part_of=ForAll([X,Y], P(X,Y) == ForAll(Z, Implies(C(Z,X), C(Z,Y))))

################################
# OVERLAPS 
# O(X,Y) : exists Z P(Z, X) /\ P(Z, Y) 
################################

overlaps=ForAll([X,Y], O(X,Y) == Exists(Z, And(P(Z,X), P(Z,Y))))

################################
# EQUAL TO 
# E(X,Y) : P(X, Y ) /\ P(Y, X ) 
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
s.add(And(reflexivity, symmetry, part_of, proper_part, proper_part_i, partial_overlap, discrete_from, equal_to, overlaps))


A = Const('A', Region)
B = Const('B', Region)
F = Const('F', Region)

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
