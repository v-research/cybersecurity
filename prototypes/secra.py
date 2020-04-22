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
# add the 5 relation of rcc5 to the solver
################################
def rcc_five(solver, regions_and_subregions, P, O, EQ, PP, PO, PPi, DR):
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


def get_region_type(region):
    if(str(region).startswith("A")):
        regiontype="assertion"
    elif(str(region).startswith("B")):
        regiontype="belief"
    elif(str(region).startswith("F")):
        regiontype="fact"
    else:
        regiontype="unknown"
    return regiontype

#input
# -spec: string with the name of the package of the spec
#output
# -component_constraints is a dictionary with entries:
# --components updated with regions (assertions, beliefs, and facts)
# --constraints defining an equality constraint between the LHS and RHS of each
#       flow (there is a flow from the out/input port to/from the channel) and
#       sub-regions of components owned by an agent
def create_regions_from_xmi(spec):
    components_flows=get_components_from_xmi(spec)
    components=components_flows['components']
    flows=components_flows['flows']

    region_id=0
    for ck,cv in components.items():
        if(cv['type']=="agent"):
            cv['regions']={}
            cv['regions']['assertion']=Const("A"+str(region_id),Region)
            cv['regions']['belief']=Const("B"+str(region_id),Region)
            cv['regions']['fact']=Const("F"+str(region_id),Region)
        elif(cv['type']=="inputport"):
            cv['regions']={}
            cv['regions']['input']=Const("A"+str(region_id),Region)
            cv['regions']['output']=Const("B"+str(region_id),Region)
        elif(cv['type']=="outputport"):
            cv['regions']={}
            cv['regions']['input']=Const("B"+str(region_id),Region)
            cv['regions']['output']=Const("A"+str(region_id),Region)
        elif(cv['type']=="funblock" or cv['type']=="inputsocket" or cv['type']=="outputsocket"):
            cv['regions']={}
            cv['regions']['input']=Const("B"+str(region_id),Region)
            region_id+=1
            cv['regions']['output']=Const("B"+str(region_id),Region)
        elif(cv['type']=="channel"):
            cv['regions']={}
            cv['regions']['input']=Const("A"+str(region_id),Region)
            region_id+=1
            cv['regions']['output']=Const("A"+str(region_id),Region)
        #each base is considered to be an input fact and an output belief
        elif(cv['type']=="base"):
            cv['regions']={}
            cv['regions']['output']=Const("B"+str(region_id),Region)
            cv['regions']['input']=Const("F"+str(region_id),Region)
        else:
            continue

        region_id+=1

    #each flow equates beliefs
    for fk,fv in flows.items():
        for r in fv: #fk->r is a flow
            #constraints.append(components[fk]['regions']['output']==components[r]['regions']['input'])
            components[fk]['regions']['output']=components[r]['regions']['input']

    poset_graph={}
    constraints=[]    
    #each agent's beliefs encompass the beliefs resulting from its components and the assertions of its ports
    for c in components.values():
        if(c['type']=="agent"):
            for c1 in components.values():
                if(c1['owner']==c['name']):
                    for r in c1['regions'].values():
                        constraints.append(P(c['regions'][get_region_type(r)],r))
                        #DEBUG
                        if(c['regions'][get_region_type(r)] in poset_graph):
                            poset_graph[c['regions'][get_region_type(r)]].add(r)
                        else:
                            s=set()
                            s.add(r)
                            poset_graph[c['regions'][get_region_type(r)]]=s

    return {'components':components,'constraints':constraints,'poset':poset_graph}

# Print iterations progress
# taken from (thanks Greenstick):
# https://stackoverflow.com/questions/3173320/text-progress-bar-in-the-console
def printProgressBar (iteration, total, prefix = '', suffix = '', decimals = 1, length = 100, fill = '█', printEnd = "\r"):
    """
    Call in a loop to create terminal progress bar
    @params:
        iteration   - Required  : current iteration (Int)
        total       - Required  : total iterations (Int)
        prefix      - Optional  : prefix string (Str)
        suffix      - Optional  : suffix string (Str)
        decimals    - Optional  : positive number of decimals in percent complete (Int)
        length      - Optional  : character length of bar (Int)
        fill        - Optional  : bar fill character (Str)
        printEnd    - Optional  : end character (e.g. "\r", "\r\n") (Str)
    """
    percent = ("{0:." + str(decimals) + "f}").format(100 * (iteration / float(total)))
    filledLength = int(length * iteration // total)
    bar = fill * filledLength + '-' * (length - filledLength)
    print('\r%s |%s| %s%% %s' % (prefix, bar, percent, suffix), end = printEnd)
    # Print New Line on Complete
    if iteration == total:
        print()

def print_poset(regions,poset):
    f=open("poset.dot","w+")
    f.write("digraph G {\n")

    for r in regions:
        if(r in poset.keys()):
            continue
        elif(r in poset.items()):
            continue
        else:
            f.write("%s\n"%r)

    for k,v in poset.items():
        for v1 in v:
            f.write("%s -> %s\n"%(k,v1))

    f.write("\n}")
    f.close()

spec="UC1-CPS"
solver=Solver()
z3.set_param('parallel.enable', True)
z3.set_param('parallel.threads.max', 32)
Region = DeclareSort('Region')

P  = Function('P', Region, Region, BoolSort())
O  = Function('O', Region, Region, BoolSort())
EQ = Function('EQ', Region, Region, BoolSort())
DR = Function('DR', Region, Region, BoolSort())
PO = Function('PO', Region, Region, BoolSort())
PP = Function('PP', Region, Region, BoolSort())
PPi= Function('Pi', Region, Region, BoolSort())

print("parse package %s in XMI and calculate Regions"%spec)
components_constraints=create_regions_from_xmi(spec)
print("done\n")

# create list of unique regions (and subregions) of the spec
# as a (time) speedup this can be an output of create_regions_from_xmi()
regions=set()
for c in components_constraints['components'].values():
    for r in c['regions'].values():
        regions.add(r)
#this may not be the most elegant solution...
regions=list(regions)
print("there are %s different Regions in %s"%(len(regions),spec))

#import pprint
#pprint.pprint(components_constraints)
#print_poset(regions,components_constraints['poset'])
#sys.exit(1)

print("add constraints on regions")
for c in components_constraints['constraints']:
    solver.add(c)
    print(c)
print("done\n")

# add topology to solver
print("add topology")
topology(solver, regions, P)
print("done\n")

# add rcc5 to solver
print("add rcc5")
rcc_five(solver, regions, P, O, EQ, PP, PO, PPi, DR)
print("done\n")

#generates all the possible pairs of regions 
pairs_regions=[]
for i in range(len(regions)):
    for j in range(i+1,len(regions)):
        pairs_regions.append([regions[i],regions[j]])

#create a list of rcc5 relation per each pair of regions
rcc5=[EQ,PP,PPi,PO,DR]
itertables = []
for i in pairs_regions:
    itertables.append(rcc5)

#import pprint
#pp=pprint.PrettyPrinter(indent=0)
#pp.pprint(itertables)

counter=1
counter_sat=0
counter_unsat=0
counter_unknown=0

print("pairs of regions: ",len(pairs_regions))
print("possible scenarios: ",len(itertables)**len(rcc5))
#itertools creates the cartesian product on the vector of rcc5 relations
#total_scenarios=len(list(itertools.product(*itertables)))
f=open(spec+".out","w+")
f.write("spec: %s\n"%spec)
f.write("pairs of regions: %s\n"%str(len(pairs_regions)))
f.write("possible scenarios: %s\n\n"%str(len(itertables)**len(rcc5)))
for t in itertools.product(*itertables):
    printProgressBar(counter,len(itertables)**len(rcc5),decimals=12)
    array_scenario=[]
    for i in range(len(t)):
        array_scenario.append(t[i](pairs_regions[i]))
    scenario=And(array_scenario)

    solver.push()
    solver.add(scenario)
    check=solver.check()

    if(check == unsat):
        counter_unsat+=1
    if(check == unknown):
        counter_unknown+=1
    if(check == sat):
        #if(check == sat):
        #    print(solver.model())
        #else:
        #    print(solver.unsat_core())
        counter_sat+=1

    #TODO 
    #https://stackoverflow.com/questions/14628279/z3-convert-z3py-expression-to-smt-lib2/14629021#14629021
    #https://stackoverflow.com/questions/19569431/z3py-print-large-formula-with-144-variables
    f.write("%d %s\n %s\n\n"%(counter, check, str(scenario).replace('\n','')))
    solver.pop()

    counter+=1

statistics="\n********\nSTATISTICS\n\nscenarios=%d\nsat=%d\nunsat=%d"%(counter-1,counter_sat,counter_unsat)
if(counter_unknown != 0):
    statistics+="\nunknown=%d"%unknown

f.write("\n",statistics)
f.close()

#print("\nPrint solver?[y/n]")
#answer=input()
#if(answer == 'y'):
#    print(solver)
