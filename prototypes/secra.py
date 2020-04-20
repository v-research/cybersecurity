#!/usr/bin/python3
#author: Marco Rocchetto @V-Research

#requirements
# 1) z3 python API (https://github.com/Z3Prover/z3/blob/master/README.md)

import sys
from z3 import *
import scipy.special
import itertools
from parse_model import get_components_from_xmi

################################
# since we unfold the quantifiers we have to calculate
# the (minimal) number of subregions of A, B, and F that allows
# Z3 to find a model that satisfies the agent configuration
# 
# For example, if we have A,B,F and no subregions of those 3 regions 
# there is no model that satisfies PO(A,B) /\ PO(B,F) /\ PO(A,F)
# since PO(A,B) <-> PP(A,B) if A has no subregions 
#
# requires scipy for binomial calculation: pip install scipy
# otherwise download wheel from https://pypi.python.org/pypi/scipy
# and install it with pip install <downloaded-file>
################################
def calculate_regions(regions, Region):
    region_of_subregions=[]
    for k in range(1,len(regions)):
        counter=0
        for i in range(int(scipy.special.binom(len(regions), (k+1)))):
            subregion="subregion_%s_%d"%((k+1), counter)
            region_of_subregions.append(Const(subregion, Region))
            #print("%d - (%d %d)=%d"%(i,len(regions),(k+1),int(scipy.special.binom(len(regions), (k+1)))))
            counter+=1
        
    return region_of_subregions

def topology(solver, regions_and_subregions, P):
    ################################
    # PART OF
    ################################
    
    for s in regions_and_subregions:
        #solver.add(P(s,s))
        solver.assert_and_track(P(s,s), str("reflexivity(%s)"%s))
    
    for s1 in regions_and_subregions:
        for s2 in regions_and_subregions:
            #solver.add(Implies(And(P(s1,s2),P(s2,s1)), s1==s2))
            solver.assert_and_track(Implies(And(P(s1,s2),P(s2,s1)), s1==s2), str("asymmetry(%s,%s)"%(s1,s2)))
    
    for s1 in regions_and_subregions:
        for s2 in regions_and_subregions:
            for s3 in regions_and_subregions:
               #solver.add(Implies(And(P(s1,s2),P(s2,s3)), P(s1,s3)))
               solver.assert_and_track(Implies(And(P(s1,s2),P(s2,s3)), P(s1,s3)), str("transitivity(%s,%s,%s)"%(s1,s2,s3)))

################################
# with mereotopology we first define connects with and then part of
################################
def mereotopology(solver, regions_and_subregions, C, P):
    ################################
    # CONNECTS WITH
    # define here the relation C (primitive binary relation called connects with)  
    # which is reflexive and symmetric 
    ################################
    
    for s in regions_and_subregions:
        #solver.add(C(s,s))
        solver.assert_and_track(C(s,s), str("riflexivity(%s,%s)"%(s,s)))
    
    for s1 in regions_and_subregions:
        for s2 in regions_and_subregions:
            #solver.add(C(s1,s2)==C(s2,s1))
            solver.assert_and_track(C(s1,s2)==C(s2,s1), str("symmetry(%s,%s)"%(s1,s2)))
    
    ################################
    # PART OF
    # P(X,Y) : forall Z C(Z,X) => C(Z,Y)
    ################################
    
    for s1 in regions_and_subregions:
        for s2 in regions_and_subregions:
            array=[]
            for s3 in regions_and_subregions:
                array.append(Implies(C(s3,s1), C(s3,s2)))
            #solver.add(P(s1,s2) == Implies(C(s3,s1), C(s3,s2))) 
            solver.assert_and_track(P(s1,s2) == And(array), str("P(%s,%s) and Z=%s"%(s1,s2,s3))) 


################################
# add the 5 relation of rcc5 to the solver
################################
def rcc_five(solver, regions_and_subregions, C, P, O, EQ, PP, PO, PPi, DR):
    ################################
    # OVERLAPS 
    # O(X,Y) : exists Z P(Z, X) /\ P(Z, Y) 
    ################################
    for s1 in regions_and_subregions:
        for s2 in regions_and_subregions:
            array=[]
            for s3 in regions_and_subregions:
                array.append(And(P(s3,s1),P(s3,s2)))
            #solver.add(O(s1,s2) == Or(array)) 
            solver.assert_and_track(O(s1,s2) == Or(array), str("O(%s,%s) and Z=%s"%(s1,s2,s3))) 
    
    ################################
    # EQUAL TO 
    # EQ(X,Y) : P(X, Y) /\ P(Y, X) 
    ################################
    for s1 in regions_and_subregions:
        for s2 in regions_and_subregions:
            #solver.add(EQ(s1,s2) == And(P(s1,s2), P(s2,s1)))
            solver.assert_and_track(EQ(s1,s2) == And(P(s1,s2), P(s2,s1)), str("EQ(%s,%s)"%(s1,s2)))
    
    ################################
    # DISCRETE FROM
    # DR(X,Y) : not O(X,Y)
    ################################
    for s1 in regions_and_subregions:
        for s2 in regions_and_subregions:
            #solver.add(DR(s1,s2) == Not(O(s1,s2)))
            solver.assert_and_track(DR(s1,s2) == Not(O(s1,s2)), str("DR(%s,%s)"%(s1,s2)))
    
    ################################
    # PARTIAL OVERLAP
    # PO(X,Y) : O(X, Y) /\ (not P(X, Y)) /\ (not P(Y, X))
    ################################
    for s1 in regions_and_subregions:
        for s2 in regions_and_subregions:
            #solver.add(PO(s1,s2) == And(O(s1,s2), Not(P(s1,s2)), Not(P(s2,s1))))
            solver.assert_and_track(PO(s1,s2) == And(O(s1,s2), Not(P(s1,s2)), Not(P(s2,s1))), str("PO(%s,%s)"%(s1,s2)))
    
    ################################
    # PROPER PART OF 
    # PP(X,Y) : P(X, Y) /\ (not P(Y, X)) 
    ################################
    for s1 in regions_and_subregions:
        for s2 in regions_and_subregions:
            #solver.add(PP(s1,s2) == And(P(s1,s2), Not(P(s2,s1))))
            solver.assert_and_track(PP(s1,s2) == And(P(s1,s2), Not(P(s2,s1))), str("PP(%s,%s)"%(s1,s2)))
    
    ################################
    # INVERSE OF PROPER PART OF 
    # PPi(X,Y) : P(Y, X) /\ (not P(X, Y)) 
    ################################
    for s1 in regions_and_subregions:
        for s2 in regions_and_subregions:
            #solver.add(PPi(s1,s2) == PP(s2, s1)) #  And(P(s2,s1), Not(P(s1,s2))))
            solver.assert_and_track(PPi(s1,s2) == PP(s2, s1), str("PPi(%s,%s)"%(s1,s2))) #  And(P(s2,s1), Not(P(s1,s2))))

#input
# -spec: string with the name of the package of the spec
#output
# -component_constraints is a dictionary with two entries:
# --components updated with regions (assertions, beliefs, and facts)
# --constraints defining an equality constraint between the LHS and RHS of each flow, except for the flow in the channel
def create_regions_from_xmi(spec):
    components_flows=get_components_from_xmi(spec)
    components=components_flows['components']
    flows=components_flows['flows']

    region2components={}
    region_id=0
    for ck,cv in components.items():
        if(cv['type']=="agent"):
            region2components[ck]=region_id
            cv['regions']={}
            cv['regions']['assertion']=Const("A"+str(region_id),Region)
            cv['regions']['belief']=Const("B"+str(region_id),Region)
            cv['regions']['fact']=Const("F"+str(region_id),Region)
        elif(cv['type']=="inputport"):
            region2components[ck]=region_id
            cv['regions']={}
            cv['regions']['input']=Const("A"+str(region_id),Region)
            cv['regions']['output']=Const("B"+str(region_id),Region)
        elif(cv['type']=="outputport"):
            region2components[ck]=region_id
            cv['regions']={}
            cv['regions']['input']=Const("B"+str(region_id),Region)
            cv['regions']['output']=Const("A"+str(region_id),Region)
        elif(cv['type']=="funblock" or cv['type']=="inputsocket" or cv['type']=="outputsocket"):
            region2components[ck]=region_id
            cv['regions']={}
            cv['regions']['input']=Const("Bi"+str(region_id),Region)
            cv['regions']['output']=Const("Bo"+str(region_id),Region)
        elif(cv['type']=="channel"):
            region2components[ck]=region_id
            cv['regions']={}
            cv['regions']['input']=Const("Ai"+str(region_id),Region)
            cv['regions']['output']=Const("Ao"+str(region_id),Region)

        #we do not support assertions, beliefs, or facts in the spec
        #elif(cv['type']=="belief"):
        #    region2components[ck]=region_id
        #    cv['regions']={}
        #    cv['regions']['belief']=Const("B"+str(region_id),Region)
        #elif(cv['type']=="fact"):
        #    region2components[ck]=region_id
        #    cv['regions']={}
        #    cv['regions']['fact']=Const("F"+str(region_id),Region)
        #elif(cv['type']=="assertion"):
        #    region2components[ck]=region_id
        #    cv['regions']={}
        #    cv['regions']['assertion']=Const("A"+str(region_id),Region)

        #each base is considered to be an input fact and an output belief
        elif(cv['type']=="base"):
            region2components[ck]=region_id
            cv['regions']={}
            cv['regions']['output']=Const("B"+str(region_id),Region)
            cv['regions']['input']=Const("F"+str(region_id),Region)
        else:
            continue

        region_id+=1

    #DEBUG
    import pprint
    pp=pprint.PrettyPrinter(indent=0)
    pp.pprint(components)

    constraints=[]    
    #each flow equates beliefs
    for fk,fv in flows.items():
        for r in fv: #fk->r is a flow
            #print(components[fk]['name'],components[fk]['type'],components[r]['name'],components[r]['type'])
            #print(components[fk]['regions']['output']==components[r]['regions']['input'])
            #print()
            constraints.append(components[fk]['regions']['output']==components[r]['regions']['input'])

    #each agent's beliefs encompass the beliefs resulting from its components and the assertions of its ports
    #each channel_lhs_A == outputport_A and channel_rhs_A == inputport_A
    #for c in components:
    #    if(c['type']=="channel"):
    #        constraints.append(

    print(constraints)
    return {'components':components,'constraints':constraints}


spec="UC1-CPS"
solver=Solver()
z3.set_param('parallel.enable', True)
z3.set_param('parallel.threads.max', 32)
Region = DeclareSort('Region')

C  = Function('C', Region, Region, BoolSort())
P  = Function('P', Region, Region, BoolSort())
O  = Function('O', Region, Region, BoolSort())
EQ = Function('EQ', Region, Region, BoolSort())
DR = Function('DR', Region, Region, BoolSort())
PO = Function('PO', Region, Region, BoolSort())
PP = Function('PP', Region, Region, BoolSort())
PPi= Function('Pi', Region, Region, BoolSort())

components_constraints=create_regions_from_xmi(spec)
sys.exit(1)

Asr = Const('Asr', Region)
Ars = Const('Ars', Region)
Bs = Const('Bs', Region)
Br = Const('Br', Region)
F = Const('F', Region)

regions=[Asr,Ars,Bs,Br,F]

regions_and_subregions=regions + calculate_regions(regions, Region)

# add partOf to solver
if(mereo_topology=="mereotopology"):
    print("MEREOTOPOLOGY")
    mereotopology(solver, regions_and_subregions, C, P)
elif(mereo_topology=="topology"):
    print("TOPOLOGY")
    topology(solver, regions_and_subregions, P)

# add rcc5 to the solver
rcc_five(solver, regions_and_subregions, C, P, O, EQ, PP, PO, PPi, DR)

################################
# AGENT
################################

#from array of regions generates pairs of regions
#pairs_regions=[[A, B], [B, F], [A, F]]
pairs_regions=[]
for i in range(len(regions)):
    for j in range(i+1,len(regions)):
        pairs_regions.append([regions[i],regions[j]])

#generates all the agents
rcc5=[EQ,PP,PPi,PO,DR]
itertables = []
for i in pairs_regions:
    itertables.append(rcc5)

counter=1
counter_sat=0
counter_unsat=0
counter_unknown=0

for t in itertools.product(*itertables):
    array_agent=[]
    for i in range(len(t)):
        array_agent.append(t[i](pairs_regions[i]))
    agent=And(array_agent)

    solver.push()
    solver.add(agent)
    check=solver.check()

    if(check == unsat):
        counter_unsat+=1
    if(check == unknown):
        counter_unknown+=1
    if(check == sat):
        offregion1=' '*(5-len(str(counter)))
        offregion2=' '*(12-len(str(check)))
        #if(check == sat):
        #    print(solver.model())
        #else:
        #    print(solver.unsat_core())
        counter_sat+=1

    print("%d %s %s %s %s"%(counter, offregion1, check, offregion2, str(agent).replace('\n','')))
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
