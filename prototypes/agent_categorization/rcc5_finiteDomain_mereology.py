from z3 import *
import scipy.special
import itertools

################################
# this method returns the rcc5 satisfiability table 
# (see Section 5.2 in "Santaca et al., A Topological Categorization of Agents for the
#   Definition of Attack States in Multi-Agent Systems")
# http://marcorocchetto.eu/pub/categorizationEUMAS16.pdf
################################
def rcc_five_sat_table(x,y,z,EQ,PP,PO,PPi,DR):
    rcc5_table=[]
    
    #DR DR
    rcc5_table.append(And(DR(x,y),DR(y,z),DR(x,z)))
    rcc5_table.append(And(DR(x,y),DR(y,z),PP(x,z)))
    rcc5_table.append(And(DR(x,y),DR(y,z),PO(x,z)))
    rcc5_table.append(And(DR(x,y),DR(y,z),PPi(x,z)))
    rcc5_table.append(And(DR(x,y),DR(y,z),EQ(x,z)))
    #DR PO
    rcc5_table.append(And(DR(x,y),PO(y,z),DR(x,z)))
    rcc5_table.append(And(DR(x,y),PO(y,z),PO(x,z)))
    rcc5_table.append(And(DR(x,y),PO(y,z),PP(x,z)))
    #DR EQ
    rcc5_table.append(And(DR(x,y),EQ(y,z),DR(x,z)))
    #DR PP
    rcc5_table.append(And(DR(x,y),PP(y,z),DR(x,z)))
    rcc5_table.append(And(DR(x,y),PP(y,z),PO(x,z)))
    rcc5_table.append(And(DR(x,y),PP(y,z),PP(x,z)))
    #DR PPi
    rcc5_table.append(And(DR(x,y),PPi(y,z),DR(x,z)))

    #PO DR
    rcc5_table.append(And(PO(x,y),DR(y,z),DR(x,z)))
    rcc5_table.append(And(PO(x,y),DR(y,z),PO(x,z)))
    rcc5_table.append(And(PO(x,y),DR(y,z),PPi(x,z)))
    #PO PO
    rcc5_table.append(And(PO(x,y),PO(y,z),DR(x,z)))
    rcc5_table.append(And(PO(x,y),PO(y,z),PO(x,z)))
    rcc5_table.append(And(PO(x,y),PO(y,z),PP(x,z)))
    rcc5_table.append(And(PO(x,y),PO(y,z),PPi(x,z)))
    rcc5_table.append(And(PO(x,y),PO(y,z),EQ(x,z)))
    #PO EQ
    rcc5_table.append(And(PO(x,y),EQ(y,z),PO(x,z)))
    #PO PP
    rcc5_table.append(And(PO(x,y),PP(y,z),PO(x,z)))
    rcc5_table.append(And(PO(x,y),PP(y,z),PP(x,z)))
    #PO PPi
    rcc5_table.append(And(PO(x,y),PPi(y,z),DR(x,z)))
    rcc5_table.append(And(PO(x,y),PPi(y,z),PO(x,z)))
    rcc5_table.append(And(PO(x,y),PPi(y,z),PPi(x,z)))

    #EQ DR
    rcc5_table.append(And(EQ(x,y),DR(y,z),DR(x,z)))
    #EQ PO
    rcc5_table.append(And(EQ(x,y),PO(y,z),PO(x,z)))
    #EQ EQ 
    rcc5_table.append(And(EQ(x,y),EQ(y,z),EQ(x,z)))
    #EQ PP 
    rcc5_table.append(And(EQ(x,y),PP(y,z),PP(x,z)))
    #EQ PPi 
    rcc5_table.append(And(EQ(x,y),PPi(y,z),PPi(x,z)))

    #PPi DR
    rcc5_table.append(And(PPi(x,y),DR(y,z),DR(x,z)))
    rcc5_table.append(And(PPi(x,y),DR(y,z),PO(x,z)))
    rcc5_table.append(And(PPi(x,y),DR(y,z),PPi(x,z)))
    #PPi PO
    rcc5_table.append(And(PPi(x,y),PO(y,z),PO(x,z)))
    rcc5_table.append(And(PPi(x,y),PO(y,z),PPi(x,z)))
    #PPi EQ
    rcc5_table.append(And(PPi(x,y),EQ(y,z),PPi(x,z)))
    #PPi PP
    rcc5_table.append(And(PPi(x,y),PP(y,z),PO(x,z)))
    rcc5_table.append(And(PPi(x,y),PP(y,z),EQ(x,z)))
    rcc5_table.append(And(PPi(x,y),PP(y,z),PP(x,z)))
    rcc5_table.append(And(PPi(x,y),PP(y,z),PPi(x,z)))
    #PPi PPi
    rcc5_table.append(And(PPi(x,y),PPi(y,z),PPi(x,z)))

    #PP DR
    rcc5_table.append(And(PP(x,y),DR(y,z),DR(x,z)))
    #PP PO
    rcc5_table.append(And(PP(x,y),PO(y,z),DR(x,z)))
    rcc5_table.append(And(PP(x,y),PO(y,z),PO(x,z)))
    rcc5_table.append(And(PP(x,y),PO(y,z),PP(x,z)))
    #PP EQ
    rcc5_table.append(And(PP(x,y),EQ(y,z),PP(x,z)))
    #PP PP
    rcc5_table.append(And(PP(x,y),PP(y,z),PP(x,z)))
    #PP PPi
    rcc5_table.append(And(PP(x,y),PPi(y,z),EQ(x,z)))
    rcc5_table.append(And(PP(x,y),PPi(y,z),DR(x,z)))
    rcc5_table.append(And(PP(x,y),PPi(y,z),PO(x,z)))
    rcc5_table.append(And(PP(x,y),PPi(y,z),PP(x,z)))
    rcc5_table.append(And(PP(x,y),PPi(y,z),PPi(x,z)))

    return rcc5_table

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
        solver.assert_and_track(P(s,s), str("riflexivity(%s)"%s))
    
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
    A = Const('A', Set)
    B = Const('B', Set)
    F = Const('F', Set)
    
    sets=[A,B,F]
    
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
    pairs_sets=[[A, B], [B, F], [A, F]]
    #pairs_sets=[]
    #for i in range(len(sets)):
    #    for j in range(i+1,len(sets)):
    #        pairs_sets.append([sets[i],sets[j]])
    
    #generates all the agents
    rcc5=[EQ,PP,PPi,PO,DR]
    itertables = []
    for i in pairs_sets:
        itertables.append(rcc5)
    
    counter=1
    counter_sat=0
    counter_unsat=0
    counter_unknown=0
    counter_correct_sat=0
    counter_correct_unsat=0
    k=1
    rcc5_sat_table=rcc_five_sat_table(A,B,F,EQ,PP,PO,PPi,DR)
    
    for t in itertools.product(*itertables):
        array_agent=[]
        for i in range(len(t)):
            array_agent.append(t[i](pairs_sets[i]))
        agent=And(array_agent)
    
        solver.push()
        solver.add(agent)
        check=solver.check()
    
        correct=False
        rcc5_table_sat=False
        for row in rcc5_sat_table:
            #print("%s = %s"%(str(row),str(agent)))
            if(str(row) == str(agent)):
                rcc5_table_sat=True
    
        if(check == unsat):
            counter_unsat+=1
            #print("a %s"%solver.unsat_core())
            if(not rcc5_table_sat):
                counter_correct_unsat+=1
                correct=True
        if(check == unknown):
            counter_unknown+=1
        if(check == sat):
            counter_sat+=1
            if(rcc5_table_sat):
                counter_correct_sat+=1
                correct=True
        solver.pop()
    
        offset1=' '*(5-len(str(counter)))
        offset2=' '*(12-len(str(check)))
        if(correct):
            print("%d %s %s %s %s"%(counter, offset1, check, offset2, agent))
        else:
            print("%d %s %s %s %s - %s"%(counter, offset1, check, offset2, agent, correct))
            if(check == sat):
                print(solver.model())
            else:
                print(solver.unsat_core())
    
    
        counter+=1
    
    print("\n********\nSTATISTICS\n\nagents=%d, correct=%d\nsat=%d, correct=%d\nunsat=%d, correct=%d\nunknown=%d"%(counter-1,(counter_correct_sat+counter_correct_unsat),counter_sat,counter_correct_sat,counter_unsat,counter_correct_unsat,counter_unknown))
    print("\nPrint solver?[y/n]")
    answer=input()
    if(answer == 'y'):
        print(solver)
    else:
        return

main("topology")
