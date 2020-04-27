#!/usr/bin/python3
#author: Marco Rocchetto @V-Research

#requirements
# 1) z3 python API (https://github.com/Z3Prover/z3/blob/master/README.md)

import sys
import time
from z3 import *
import scipy.special
import itertools
from parse_model import get_components_from_xmi
#DEBUG
import pprint

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
#def calculate_subregions(regions, Base):
#    region_of_subregions=[]
#    for k in range(1,len(regions)):
#        counter=0
#        for i in range(int(scipy.special.binom(len(regions), (k+1)))):
#            subregion="subregion_%s_%d"%((k+1), counter)
#            region_of_subregions.append(Const(subregion, Base))
#            #print("%d - (%d %d)=%d"%(i,len(regions),(k+1),int(scipy.special.binom(len(regions), (k+1)))))
#            counter+=1
#        
#    return region_of_subregions

# each region in a pair needs to have
# a subregion to share and one to keep
# to be able to use RCC5. This would not
# be necessary if we didn't unfold quantifiers;
# but unfolding prevents Z3 from unswering unknown 
# instead of sat/unsat
def add_minimal_subregions(pairs,solver):
    num_subreg=0
    regions=set()
    subregions=set()
    for p1,p2 in pairs:

        regions.add(p1)
        for i in range(2):
            s_name="S"+str(p1)+"_"+str(num_subreg)
            s=Const(s_name,Base)
            subregions.add(s)
            solver.assert_and_track(P(s,p1), str("subregion(%s,%s)"%(s,p1)))
            num_subreg+=1

        regions.add(p2)
        for i in range(2):
            s_name="S"+str(p2)+"_"+str(num_subreg)
            s=Const(s_name,Base)
            subregions.add(s)
            solver.assert_and_track(P(s,p2), str("subregion(%s,%s)"%(s,p2)))
            num_subreg+=1
    return {'regions':regions,'subregions':subregions}

def topology(solver, regions_and_subregions, P):
    ################################
    # PART OF
    ################################
    
    counter=0
    l=len(regions_and_subregions)
    tot=l**3
    for s1 in regions_and_subregions:
        #solver.add(P(s,s))
        solver.assert_and_track(P(s1,s1), str("reflexivity(%s1)"%s1))
        for s2 in regions_and_subregions:
            #solver.add(Implies(And(P(s1,s2),P(s2,s1)), s1==s2))
            solver.assert_and_track(Implies(And(P(s1,s2),P(s2,s1)), s1==s2), str("asymmetry(%s,%s)"%(s1,s2)))
            for s3 in regions_and_subregions:
                #solver.add(Implies(And(P(s1,s2),P(s2,s3)), P(s1,s3)))
                solver.assert_and_track(Implies(And(P(s1,s2),P(s2,s3)), P(s1,s3)), str("transitivity(%s,%s,%s)"%(s1,s2,s3)))
                printProgressBar(counter,tot,decimals=2)
                counter+=1

    #for s in regions_and_subregions:
    #    #solver.add(P(s,s))
    #    solver.assert_and_track(P(s,s), str("reflexivity(%s)"%s))
    #
    #for s1 in regions_and_subregions:
    #    for s2 in regions_and_subregions:
    #        #solver.add(Implies(And(P(s1,s2),P(s2,s1)), s1==s2))
    #        solver.assert_and_track(Implies(And(P(s1,s2),P(s2,s1)), s1==s2), str("asymmetry(%s,%s)"%(s1,s2)))
    #
    #for s1 in regions_and_subregions:
    #    for s2 in regions_and_subregions:
    #        for s3 in regions_and_subregions:
    #           #solver.add(Implies(And(P(s1,s2),P(s2,s3)), P(s1,s3)))
    #           solver.assert_and_track(Implies(And(P(s1,s2),P(s2,s3)), P(s1,s3)), str("transitivity(%s,%s,%s)"%(s1,s2,s3)))


################################
# add the 5 relation of rcc5 to the solver
################################
def rcc_five(solver, regions, P, O, EQ, PP, PO, PPi, DR):
    ################################
    # OVERLAPS 
    # O(X,Y) : exists Z P(Z, X) /\ P(Z, Y) 
    ################################
    for s1 in regions:
        for s2 in regions:
            array=[]
            for s3 in regions:
                array.append(And(P(s3,s1),P(s3,s2)))
            #solver.add(O(s1,s2) == Or(array)) 
            solver.assert_and_track(O(s1,s2) == Or(array), str("O(%s,%s) and Z=%s"%(s1,s2,s3))) 
    
    ################################
    # EQUAL TO 
    # EQ(X,Y) : P(X, Y) /\ P(Y, X) 
    ################################
    for s1 in regions:
        for s2 in regions:
            #solver.add(EQ(s1,s2) == And(P(s1,s2), P(s2,s1)))
            solver.assert_and_track(EQ(s1,s2) == And(P(s1,s2), P(s2,s1)), str("EQ(%s,%s)"%(s1,s2)))
    
    ################################
    # DISCRETE FROM
    # DR(X,Y) : not O(X,Y)
    ################################
    for s1 in regions:
        for s2 in regions:
            #solver.add(DR(s1,s2) == Not(O(s1,s2)))
            solver.assert_and_track(DR(s1,s2) == Not(O(s1,s2)), str("DR(%s,%s)"%(s1,s2)))
    
    ################################
    # PARTIAL OVERLAP
    # PO(X,Y) : O(X, Y) /\ (not P(X, Y)) /\ (not P(Y, X))
    ################################
    for s1 in regions:
        for s2 in regions:
            #solver.add(PO(s1,s2) == And(O(s1,s2), Not(P(s1,s2)), Not(P(s2,s1))))
            solver.assert_and_track(PO(s1,s2) == And(O(s1,s2), Not(P(s1,s2)), Not(P(s2,s1))), str("PO(%s,%s)"%(s1,s2)))
    
    ################################
    # PROPER PART OF 
    # PP(X,Y) : P(X, Y) /\ (not P(Y, X)) 
    ################################
    for s1 in regions:
        for s2 in regions:
            #solver.add(PP(s1,s2) == And(P(s1,s2), Not(P(s2,s1))))
            solver.assert_and_track(PP(s1,s2) == And(P(s1,s2), Not(P(s2,s1))), str("PP(%s,%s)"%(s1,s2)))
    
    ################################
    # INVERSE OF PROPER PART OF 
    # PPi(X,Y) : P(Y, X) /\ (not P(X, Y)) 
    ################################
    for s1 in regions:
        for s2 in regions:
            #solver.add(PPi(s1,s2) == PP(s2, s1)) #  And(P(s2,s1), Not(P(s1,s2))))
            solver.assert_and_track(PPi(s1,s2) == PP(s2, s1), str("PPi(%s,%s)"%(s1,s2))) #  And(P(s2,s1), Not(P(s1,s2))))

#should we create objects with method returning a constant for Z3 of type Base? Maybe... maybe not
def get_base_type(base):
    if(str(base).startswith("A")):
        basetype="assertion"
    elif(str(base).startswith("B")):
        basetype="belief"
    elif(str(base).startswith("F")):
        basetype="fact"
    else:
        basetype="unknown"
    return basetype

#input
# -spec: string with the name of the package of the spec
#output
# -component_constraints is a dictionary with entries:
# --components updated with regions (assertions, beliefs, and facts)

# components are created with the following constraints 
# -- defining an equality constraint between the LHS and RHS of each
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
            cv['regions']['assertion']=set()
            cv['regions']['belief']=set()
        elif(cv['type']=="inputport"):
            cv['regions']={}
            cv['regions']['input']=Const("A"+str(region_id),Base)
            cv['regions']['output']=Const("B"+str(region_id),Base)
        elif(cv['type']=="outputport"):
            cv['regions']={}
            cv['regions']['input']=Const("B"+str(region_id),Base)
            cv['regions']['output']=Const("A"+str(region_id),Base)
        elif(cv['type']=="funblock" or cv['type']=="inputsocket" or cv['type']=="outputsocket"):
            cv['regions']={}
            cv['regions']['input']=Const("B"+str(region_id),Base)
            region_id+=1
            cv['regions']['output']=Const("B"+str(region_id),Base)
        elif(cv['type']=="channel"):
            cv['regions']={}
            cv['regions']['input']=Const("A"+str(region_id),Base)
            region_id+=1
            cv['regions']['output']=Const("A"+str(region_id),Base)
        #bases are beliefs related to blocks and facts related to root
        elif(cv['type']=="base"):
            cv['regions']={}
            cv['regions']['belief']=Const("B"+str(region_id),Base)
            #cv['regions']['fact']=Const("F"+str(region_id),Base)
        else:
            continue

        region_id+=1

    pprint.pprint(flows)
    #each flow equates beliefs
    for fk,fv in flows.items():
            for r in fv: #fk->r is a flow
                if(components[fk]['type']=="base"):
                    components[fk]['regions']['belief']=components[r]['regions']['input']
                elif(components[r]['type']=="base"):
                    components[fk]['regions']['output']=components[r]['regions']['belief']
                else:
                    components[fk]['regions']['output']=components[r]['regions']['input']

    #we create the agent root as a common knowledge
    common_knowledge={'name':"root",'owner':"root",'type':"root",'regions':{'fact':set()}}
    #TODO we assume no inner-components in Object diagrams
    #each agent's belief encompasses the beliefs of its components and the assertions of its ports
    #each region has a corresponding fact (which may be dr or eq)
    for cv in components.values():
        if(cv['type']=="base"):
            common_knowledge['regions']['fact'].add(Const("F_"+str(cv['regions']['belief']),Base))
            if(cv['owner']!="root"):
                components[cv['owner']]['regions']['belief'].add(cv['regions']['belief'])
        elif(cv['type']=="funblock" or cv['type']=="inputsocket" or cv['type']=="outputsocket"):
            common_knowledge['regions']['fact'].add(Const("F_"+str(cv['regions']['output']),Base))
            if(cv['owner']!="root"):
                components[cv['owner']]['regions'][get_base_type(cv['regions']['input'])].add(cv['regions']['input'])
                components[cv['owner']]['regions'][get_base_type(cv['regions']['output'])].add(cv['regions']['output'])
    components['root']=common_knowledge

    return components


def get_base_by_name(name,components):
    for c in components.values():
        if(name.startswith("A") or name.startswith("B")):
            if(c['type']=="agent"):
                for r in c['regions']['assertion']:
                    if(name==str(r)):
                        return r
                for r in c['regions']['belief']:
                    if(name==str(r)):
                        return r
        elif(name.startswith("F")):
            if(c['type']=="root"):
                for r in c['regions']['fact']:
                    if(name==str(r)):
                        return r
    return None

#generates all the possible pairs of regions 
# - (F,B) (F,A) a pair per each association fact-belief/assertion
# - (B,A) another per each port_I-port_O
# - (F,A) another per each chan_I-chan_O
# dot files contains 3 types of links:
# - flows [directional gray]
# - ownership [directional dotted]
# - pair relation (A,B), (B,F), or (A,F) [red/green/blue no-arrow]
# and the following nodes:
# - F:facts, B:beliefs, A:assertions, name:agents
def print_graph_and_calculate_pairs(components):

    f=open("poset.dot","w+")
    f.write("digraph G {\n")
    pairs=[]

    for c in components.values():
        if(c['name']=="root"):
            for fact in c['regions']['fact']:
                f.write("%s -> %s [style=dotted]\n"%("root",str(fact)))
                #if(str(fact)[2:].startswith("A")):
                #    f.write("%s -> %s [arrowhead=none, penwidth=2, label=AF, color=\"blue\"]\n"%(str(fact),str(fact)[2:]))
                #else:
                #    f.write("%s -> %s [arrowhead=none, penwidth=2, label=BF, color=\"green\"]\n"%(str(fact),str(fact)[2:]))
                f.write("%s -> %s [arrowhead=none, penwidth=2, label=BF, color=\"green\"]\n"%(str(fact),str(fact)[2:]))
                pairs.append([fact,get_base_by_name(str(fact)[2:],components)])
        elif(c['type']=="agent"):
            for r in c['regions']['assertion']:
                f.write("%s -> %s [style=dotted]\n"%(c['name'],str(r)))
            for r in c['regions']['belief']:
                f.write("%s -> %s [style=dotted]\n"%(c['name'],str(r)))
        elif(c['type']!="base"):
        #elif(c['type']=="inputport" or c['type']=="outputport" or c['type']=="channel"):
            f.write("%s -> %s [label=%s_%s, color=gray40]\n"%(c['regions']['input'],c['regions']['output'],c['name'],c['type']))
            if(c['type']=="inputport" or c['type']=="outputport"):
                f.write("%s -> %s [arrowhead=none, penwidth=2, label=AB, color=\"red\"]\n"%(c['regions']['input'],c['regions']['output']))
                pairs.append([c['regions']['input'],c['regions']['output']])
            elif(c['type']=="channel"):
                pairs.append([c['regions']['input'],c['regions']['output']])
                f.write("%s -> %s [arrowhead=none, penwidth=2, label=AA, color=\"blue\"]\n"%(c['regions']['input'],c['regions']['output']))
    
    f.write("\n}")
    f.close()
    return pairs

spec="UC1-CPS"
solver=Solver()
z3.set_param('parallel.enable', True)
z3.set_param('parallel.threads.max', 32)
#Z3 doesn't (nor any other SMT solver) support sub-sorting
#https://stackoverflow.com/questions/36933174/sort-inheritance-in-z3
#this may be of interest:
#https://stackoverflow.com/questions/12253088/how-to-check-if-a-const-in-z3-is-a-variable-or-a-value
Base = DeclareSort('Base')

P  = Function('P', Base, Base, BoolSort())
O  = Function('O', Base, Base, BoolSort())
EQ = Function('EQ', Base, Base, BoolSort())
DR = Function('DR', Base, Base, BoolSort())
PO = Function('PO', Base, Base, BoolSort())
PP = Function('PP', Base, Base, BoolSort())
PPi= Function('Pi', Base, Base, BoolSort())

# create list of unique regions (and subregions) of the spec
# as a (time) speedup this can be an output of create_regions_from_xmi()
print("parse package %s in XMI and calculate Bases"%spec)
components=create_regions_from_xmi(spec)
print("done\n")

print("calculate pairs and generate graph")
pprint.pprint(components)
pairs=print_graph_and_calculate_pairs(components)
print("%d pairs of regions\n%d configurations\n"%(len(pairs),5**(len(pairs))))

print("add constraints on regions for RCC5")
regions_subregions=add_minimal_subregions(pairs,solver)
print("addedd %d subregions"%len(regions_subregions['subregions']))

# add topology theory to solver
print("create topology [it may take a while]")
topology(solver, regions_subregions['regions'].union(regions_subregions['subregions']), P)
print("done\n")

# add rcc5 theory over regions to solver
print("add rcc5")
rcc_five(solver, regions_subregions['regions'], P, O, EQ, PP, PO, PPi, DR)
print("done\n")

#create a list of rcc5 relation per each pair of regions
rcc5=[EQ,PP,PPi,PO,DR]
itertables = []
for i in pairs:
    itertables.append(rcc5)

counter=1
counter_sat=0
counter_unsat=0
counter_unknown=0

num_pairs=len(pairs)
num_scenarios=5**len(itertables)
print("pairs of regions: ",num_pairs)
print("possible scenarios: ",num_scenarios)
#itertools creates the cartesian product on the vector of rcc5 relations
#total_scenarios=len(list(itertools.product(*itertables)))
f=open(spec+".out","w+")
f.write("spec: %s\n"%spec)
f.write("pairs of regions: %s\n"%str(num_pairs))
f.write("possible scenarios: %s\n\n"%str(num_scenarios))
avg_time=0.00000
sum_time=0.00000

#TODO restart from 
# save pairs and restart from that iteration
# https://stackoverflow.com/questions/36802314/python-itertools-product-start-from-certain
for t in itertools.product(*itertables):

    start = time.time()

    sec_avg=str(avg_time).split('.')[0]
    dec_avg=str(avg_time).split('.')[1]
    sec_sum=str(sum_time).split('.')[0]
    dec_sum=str(sum_time).split('.')[1]
    end=avg_time*(num_scenarios-counter)
    end_estimation=str(end).split('.')[0]
    printProgressBar(counter,num_scenarios,suffix="avg:"+sec_avg+"."+dec_avg[:5]+"s tot:"+sec_sum+"."+dec_sum[:2]+"s"+" end:"+end_estimation+"s",decimals=5)
    array_scenario=[]
    for i in range(len(t)):
        array_scenario.append(t[i](pairs[i]))
    scenario=And(array_scenario)

    solver.push()
    solver.add(scenario)
    check=solver.check()

    if(check == unsat):
        counter_unsat+=1
        f.write("UNSAT CORE\n")
        core=solver.unsat_core()
        for k in core:
            f.write('%s=%s\n'%(k, core[k]))
    if(check == unknown):
        counter_unknown+=1
    if(check == sat):
        counter_sat+=1
        #f.write("MODEL\n")
        #model=solver.model()
        #for k in model:
        #    f.write('%s=%s\n'%(k, model[k]))

    #TODO 
    #https://stackoverflow.com/questions/14628279/z3-convert-z3py-expression-to-smt-lib2/14629021#14629021
    #https://stackoverflow.com/questions/19569431/z3py-print-large-formula-with-144-variables
    f.write("%d %s\n %s\n\n"%(counter, check, str(scenario).replace('\n','')))
    solver.pop()

    counter+=1

    end = time.time()
    sum_time+=(end - start)
    avg_time=(sum_time/counter)

statistics="\n********\nSTATISTICS\n\nscenarios=%d\nsat=%d\nunsat=%d"%(counter-1,counter_sat,counter_unsat)
if(counter_unknown != 0):
    statistics+="\nunknown=%d"%unknown

f.write("\n",statistics)
f.close()

#print("\nPrint solver?[y/n]")
#answer=input()
#if(answer == 'y'):
#    print(solver)
