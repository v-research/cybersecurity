#!/usr/bin/python3
#author: Marco Rocchetto @V-Research

#requirements
# 1) z3 python API (https://github.com/Z3Prover/z3/blob/master/README.md)

from z3 import *
import scipy.special
import itertools

################################
# since we unfold the quantifiers we have to calculate
# the (minimal) number of subsets of A, B, and F that allows
# Z3 to find a model that satisfies the agent configuration
# 
# For example, if we have A,B,F and no subsets of those 3 sets 
# there is no model that satisfies PO(A,B) /\ PO(B,F) /\ PO(A,F)
# since PO(A,B) <-> PP(A,B) if A has no subsets 
#
# requires scipy for binomial calculation: pip install scipy
# otherwise download wheel from https://pypi.python.org/pypi/scipy
# and install it with pip install <downloaded-file>
################################
def calculate_sets(sets, Set):
    set_of_subsets=[]
    for k in range(1,len(sets)):
        counter=0
        for i in range(int(scipy.special.binom(len(sets), (k+1)))):
            subset="subset_%s_%d"%((k+1), counter)
            set_of_subsets.append(Const(subset, Set))
            #print("%d - (%d %d)=%d"%(i,len(sets),(k+1),int(scipy.special.binom(len(sets), (k+1)))))
            counter+=1
        
    return set_of_subsets

def topology(solver, sets_and_subsets, P):
    ################################
    # PART OF
    ################################
    
    for s in sets_and_subsets:
        #solver.add(P(s,s))
        solver.assert_and_track(P(s,s), str("reflexivity(%s)"%s))
    
    for s1 in sets_and_subsets:
        for s2 in sets_and_subsets:
            #solver.add(Implies(And(P(s1,s2),P(s2,s1)), s1==s2))
            solver.assert_and_track(Implies(And(P(s1,s2),P(s2,s1)), s1==s2), str("asymmetry(%s,%s)"%(s1,s2)))
    
    for s1 in sets_and_subsets:
        for s2 in sets_and_subsets:
            for s3 in sets_and_subsets:
               #solver.add(Implies(And(P(s1,s2),P(s2,s3)), P(s1,s3)))
               solver.assert_and_track(Implies(And(P(s1,s2),P(s2,s3)), P(s1,s3)), str("transitivity(%s,%s,%s)"%(s1,s2,s3)))

################################
# with mereotopology we first define connects with and then part of
################################
def mereotopology(solver, sets_and_subsets, C, P):
    ################################
    # CONNECTS WITH
    # define here the relation C (primitive binary relation called connects with)  
    # which is reflexive and symmetric 
    ################################
    
    for s in sets_and_subsets:
        #solver.add(C(s,s))
        solver.assert_and_track(C(s,s), str("riflexivity(%s,%s)"%(s,s)))
    
    for s1 in sets_and_subsets:
        for s2 in sets_and_subsets:
            #solver.add(C(s1,s2)==C(s2,s1))
            solver.assert_and_track(C(s1,s2)==C(s2,s1), str("symmetry(%s,%s)"%(s1,s2)))
    
    ################################
    # PART OF
    # P(X,Y) : forall Z C(Z,X) => C(Z,Y)
    ################################
    
    for s1 in sets_and_subsets:
        for s2 in sets_and_subsets:
            array=[]
            for s3 in sets_and_subsets:
                array.append(Implies(C(s3,s1), C(s3,s2)))
            #solver.add(P(s1,s2) == Implies(C(s3,s1), C(s3,s2))) 
            solver.assert_and_track(P(s1,s2) == And(array), str("P(%s,%s) and Z=%s"%(s1,s2,s3))) 


################################
# add the 5 relation of rcc5 to the solver
################################
def rcc_five(solver, sets_and_subsets, C, P, O, EQ, PP, PO, PPi, DR):
    ################################
    # OVERLAPS 
    # O(X,Y) : exists Z P(Z, X) /\ P(Z, Y) 
    ################################
    for s1 in sets_and_subsets:
        for s2 in sets_and_subsets:
            array=[]
            for s3 in sets_and_subsets:
                array.append(And(P(s3,s1),P(s3,s2)))
            #solver.add(O(s1,s2) == Or(array)) 
            solver.assert_and_track(O(s1,s2) == Or(array), str("O(%s,%s) and Z=%s"%(s1,s2,s3))) 
    
    ################################
    # EQUAL TO 
    # EQ(X,Y) : P(X, Y ) /\ P(Y, X ) 
    ################################
    for s1 in sets_and_subsets:
        for s2 in sets_and_subsets:
            #solver.add(EQ(s1,s2) == And(P(s1,s2), P(s2,s1)))
            solver.assert_and_track(EQ(s1,s2) == And(P(s1,s2), P(s2,s1)), str("EQ(%s,%s)"%(s1,s2)))
    
    ################################
    # DISCRETE FROM
    # DR(X,Y) : not O(X,Y)
    ################################
    for s1 in sets_and_subsets:
        for s2 in sets_and_subsets:
            #solver.add(DR(s1,s2) == Not(O(s1,s2)))
            solver.assert_and_track(DR(s1,s2) == Not(O(s1,s2)), str("DR(%s,%s)"%(s1,s2)))
    
    ################################
    # PARTIAL OVERLAP
    # PO(X,Y) : O(X, Y) /\ (not P(X, Y)) /\ (not P(Y, X))
    ################################
    for s1 in sets_and_subsets:
        for s2 in sets_and_subsets:
            #solver.add(PO(s1,s2) == And(O(s1,s2), Not(P(s1,s2)), Not(P(s2,s1))))
            solver.assert_and_track(PO(s1,s2) == And(O(s1,s2), Not(P(s1,s2)), Not(P(s2,s1))), str("PO(%s,%s)"%(s1,s2)))
    
    ################################
    # PROPER PART OF 
    # PP(X,Y) : P(X, Y) /\ (not P(Y, X)) 
    ################################
    for s1 in sets_and_subsets:
        for s2 in sets_and_subsets:
            #solver.add(PP(s1,s2) == And(P(s1,s2), Not(P(s2,s1))))
            solver.assert_and_track(PP(s1,s2) == And(P(s1,s2), Not(P(s2,s1))), str("PP(%s,%s)"%(s1,s2)))
    
    ################################
    # INVERSE OF PROPER PART OF 
    # PPi(X,Y) : P(Y, X) /\ (not P(X, Y)) 
    ################################
    for s1 in sets_and_subsets:
        for s2 in sets_and_subsets:
            #solver.add(PPi(s1,s2) == PP(s2, s1)) #  And(P(s2,s1), Not(P(s1,s2))))
            solver.assert_and_track(PPi(s1,s2) == PP(s2, s1), str("PPi(%s,%s)"%(s1,s2))) #  And(P(s2,s1), Not(P(s1,s2))))



def main(mereo_topology="topology"):
    solver=Solver()
    z3.set_param('parallel.enable', True)
    z3.set_param('parallel.threads.max', 32)
    Set = DeclareSort('Set')
    
    C  = Function('C', Set, Set, BoolSort())
    P  = Function('P', Set, Set, BoolSort())
    O  = Function('O', Set, Set, BoolSort())
    EQ = Function('EQ', Set, Set, BoolSort())
    DR = Function('DR', Set, Set, BoolSort())
    PO = Function('PO', Set, Set, BoolSort())
    PP = Function('PP', Set, Set, BoolSort())
    PPi= Function('Pi', Set, Set, BoolSort())
    
    ################################
    # SETS
    ################################
    Asr = Const('Asr', Set)
    Ars = Const('Ars', Set)
    Bs = Const('Bs', Set)
    Br = Const('Br', Set)
    F = Const('F', Set)
    
    sets=[Asr,Ars,Bs,Br,F]
    
    sets_and_subsets=sets + calculate_sets(sets, Set)
    
    # add partOf to solver
    if(mereo_topology=="mereotopology"):
        print("MEREOTOPOLOGY")
        mereotopology(solver, sets_and_subsets, C, P)
    elif(mereo_topology=="topology"):
        print("TOPOLOGY")
        topology(solver, sets_and_subsets, P)

    # add rcc5 to the solver
    rcc_five(solver, sets_and_subsets, C, P, O, EQ, PP, PO, PPi, DR)
    
    ################################
    # AGENT
    ################################
    
    #from array of sets generates pairs of sets
    #pairs_sets=[[A, B], [B, F], [A, F]]
    pairs_sets=[]
    for i in range(len(sets)):
        for j in range(i+1,len(sets)):
            pairs_sets.append([sets[i],sets[j]])
    
    #generates all the agents
    rcc5=[EQ,PP,PPi,PO,DR]
    itertables = []
    for i in pairs_sets:
        itertables.append(rcc5)
    
    counter=1
    counter_sat=0
    counter_unsat=0
    counter_unknown=0
    
    for t in itertools.product(*itertables):
        array_agent=[]
        for i in range(len(t)):
            array_agent.append(t[i](pairs_sets[i]))
        agent=And(array_agent)
    
        solver.push()
        solver.add(agent)
        check=solver.check()
    
        if(check == unsat):
            counter_unsat+=1
        if(check == unknown):
            counter_unknown+=1
        if(check == sat):
            offset1=' '*(5-len(str(counter)))
            offset2=' '*(12-len(str(check)))
            #if(check == sat):
            #    print(solver.model())
            #else:
            #    print(solver.unsat_core())
            counter_sat+=1

        print("%d %s %s %s %s"%(counter, offset1, check, offset2, str(agent).replace('\n','')))
        solver.pop()
    
        counter+=1
    
    statistics="\n********\nSTATISTICS\n\nagents=%d\nsat=%d\nunsat=%d"%(counter-1,counter_sat,counter_unsat)
    if(counter_unknown != 0):
        statistics+="\nunknown=%d"%unknown

    print(statistics)

    #print("\nPrint solver?[y/n]")
    #answer=input()
    #if(answer == 'y'):
    #    print(solver)

main("topology")
