#!/usr/bin/python3
#author: Marco Rocchetto @V-Research

#requirements
# 1) z3 python API (https://github.com/Z3Prover/z3/blob/master/README.md)

import sys
import time
from z3 import *
import scipy.special
import itertools
from parse_model import get_components_from_xmi, create_model_dot
import pprint
import xlsxwriter
import pydot

spec_package="UC1-CPS"
#spec_package="TwoGuysTalking"
xmi_filename="Engineering.xmi"

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
    pairs_array=[]
    for p1,l in pairs.items():
        for p2 in l:
            regions.add(p1)
            pairs_array.append([p1,p2])
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
    return {'regions':regions,'subregions':subregions,'pairs_array':pairs_array}

################################
# add the 5 relation of rcc5 to the solver
################################
def rcc_five(solver, regions_and_subregions, P, O, EQ, PP, PO, PPi, DR):
    ################################
    # OVERLAPS          O(X,Y) : exists Z P(Z, X) /\ P(Z, Y) 
    # EQUAL             EQ(X,Y) : P(X, Y) /\ P(Y, X) 
    # DESCRETE FROM     DR(X,Y) : not O(X,Y)
    # PARTIAL OVERLAP   PO(X,Y) : O(X, Y) /\ (not P(X, Y)) /\ (not P(Y, X))
    # PROPER PART       PP(X,Y) : P(X, Y) /\ (not P(Y, X)) 
    # PP INVERSE        PPi(X,Y) : P(Y, X) /\ (not P(X, Y)) 
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
            #solver.add(EQ(s1,s2) == And(P(s1,s2), P(s2,s1)))
            solver.assert_and_track(EQ(s1,s2) == And(P(s1,s2), P(s2,s1)), str("EQ(%s,%s)"%(s1,s2)))
            #solver.add(DR(s1,s2) == Not(O(s1,s2)))
            solver.assert_and_track(DR(s1,s2) == Not(O(s1,s2)), str("DR(%s,%s)"%(s1,s2)))
            #solver.add(PO(s1,s2) == And(O(s1,s2), Not(P(s1,s2)), Not(P(s2,s1))))
            solver.assert_and_track(PO(s1,s2) == And(O(s1,s2), Not(P(s1,s2)), Not(P(s2,s1))), str("PO(%s,%s)"%(s1,s2)))
            #solver.add(PP(s1,s2) == And(P(s1,s2), Not(P(s2,s1))))
            solver.assert_and_track(PP(s1,s2) == And(P(s1,s2), Not(P(s2,s1))), str("PP(%s,%s)"%(s1,s2)))
            #solver.add(PPi(s1,s2) == PP(s2, s1)) #  And(P(s2,s1), Not(P(s1,s2))))
            solver.assert_and_track(PPi(s1,s2) == PP(s2, s1), str("PPi(%s,%s)"%(s1,s2))) #  And(P(s2,s1), Not(P(s1,s2))))
            array=[]
            for s3 in regions_and_subregions:
                #solver.add(Implies(And(P(s1,s2),P(s2,s3)), P(s1,s3)))
                solver.assert_and_track(Implies(And(P(s1,s2),P(s2,s3)), P(s1,s3)), str("transitivity(%s,%s,%s)"%(s1,s2,s3)))
                #for OVERLAP
                array.append(And(P(s3,s1),P(s3,s2)))
                printProgressBar(counter,tot,decimals=2)
                counter+=1
            #solver.add(O(s1,s2) == Or(array)) 
            solver.assert_and_track(O(s1,s2) == Or(array), str("O(%s,%s) and Z=%s"%(s1,s2,s3))) 
    
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
# -spec_package: string with the name of the package of the spec
#output
# -component_constraints is a dictionary with entries:
# --components updated with regions (assertions, beliefs, and facts)

# components are created with the following constraints 
# -- defining an equality constraint between the LHS and RHS of each
#       flow (there is a flow from the out/input port to/from the channel) and
#       sub-regions of components owned by an agent
def create_regions_from_xmi(spec_package,xmi_filename):
    components_flows=get_components_from_xmi(spec_package,xmi=xmi_filename)
    create_model_dot(path, spec_package, components_flows['components'], components_flows['flows'])
    components=components_flows['components']
    flows=components_flows['flows']

    region_id=0
    # Each port and block has a list of inputs and a list of outputs
    # no internal structure of a block is allowed (no association between I-O) and their semantics
    # will be defined as requirements (as Z3 formulas) over facts.
    # - Channels are still unidirectional with a single flow (i.e. a channel per each information flow)
    # - Bases are also singleton
    for ck,cv in components.items():
        if(cv['type']=="agent"):
            cv['regions']={}
            cv['regions']['assertion']=set()
            cv['regions']['belief']=set()
        elif(cv['type']=="inputport"):
            cv['regions']={}
            cv['regions']['input']=set()#Const("A"+str(region_id),Base)
            cv['regions']['output']=set()#Const("B"+str(region_id),Base)
        elif(cv['type']=="outputport"):
            cv['regions']={}
            cv['regions']['input']=set()#Const("B"+str(region_id),Base)
            cv['regions']['output']=set()#Const("A"+str(region_id),Base)
        elif(cv['type']=="funblock" or cv['type']=="inputsocket" or cv['type']=="outputsocket"):
            cv['regions']={}
            cv['regions']['input']=set()#Const("B"+str(region_id),Base)
            region_id+=1
            cv['regions']['output']=set()#Const("B"+str(region_id),Base)
        elif(cv['type']=="channel"):
            cv['regions']={}
            cv['regions']['input']=Const("A"+str(region_id),Base)
            region_id+=1
            cv['regions']['output']=Const("A"+str(region_id),Base)
        elif(cv['type']=="base"):
            cv['regions']={}
            cv['regions']['belief']=Const("B"+str(region_id),Base)
        else:
            continue
        region_id+=1

    #each flow equates beliefs and add constants representing 
    #inputs/outputs in the components structures
    # you cannot have flows from agents or to agents
    multiple_outflows={}
    for fk,fv in flows.items():
        tmp_belief=None
        for r in fv: #fk->r is a flow
            if(components[fk]['type']=="outputport" and components[r]['type']=="channel"):
                components[fk]['regions']['output'].add(components[r]['regions']['input'])
                if(len(fv)>1):
                    print("ERROR cannot have multiple flows from port %s to channel"%components[fk]['name'])
            elif(components[fk]['type']=="channel" and components[r]['type']=="inputport"):
                components[r]['regions']['input'].add(components[fk]['regions']['output'])
                if(len(fv)>1):
                    print("ERROR cannot have multiple flows from channel %s to port"%components[fk]['name'])
            elif((components[fk]['type']=="funblock" or components[fk]['type']=="inputsocket" or components[fk]['type']=="outputsocket" or components[fk]['type']=="inputport") and (components[r]['type']=="funblock" or components[r]['type']=="outputsocket" or components[r]['type']=="inputsocket" or components[r]['type']=="outputport" or components[r]['type']=="inputport")):
                if(tmp_belief is None):
                    tmp_belief=Const("B"+str(region_id),Base)
                    region_id+=1
                components[fk]['regions']['output'].add(tmp_belief)
                components[r]['regions']['input'].add(tmp_belief)
            elif(components[fk]['type']=="base"):
                components[r]['regions']['input'].add(components[fk]['regions']['belief'])
            elif(components[r]['type']=="base"):
                components[fk]['regions']['input'].add(components[r]['regions']['belief'])
            else:
                print("ERROR in parsing data-flow structure")
                print("%s[%s] -> %s[%s] not supported"%(components[fk]['name'],components[fk]['type'],components[r]['name'],components[r]['type']))
                sys.exit(0)
                        
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
            for o in cv['regions']['output']:
                common_knowledge['regions']['fact'].add(Const("F_"+str(o),Base))
            if(cv['owner']!="root"):
                for i in cv['regions']['input']:
                    components[cv['owner']]['regions'][get_base_type(i)].add(i)
                for o in cv['regions']['output']:
                    components[cv['owner']]['regions'][get_base_type(o)].add(o)
        elif(cv['type']=="inputport" or cv['type']=="outputport"):
            if(cv['owner']!="root"):
                for i in cv['regions']['input']:
                    components[cv['owner']]['regions'][get_base_type(i)].add(i)
                for o in cv['regions']['output']:
                    components[cv['owner']]['regions'][get_base_type(o)].add(o)
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
def generate_graph(components):

    f=open(os.path.join(path,spec_package+"_graph.dot"),"w+")
    f.write("digraph G {\n")
    pairs={}
    num_pairs=0

    for c in components.values():
        if(c['name']=="root"):
            for fact in c['regions']['fact']:
                f.write("%s -> %s [style=dotted]\n"%("root",str(fact)))
                f.write("%s -> %s [arrowhead=none, penwidth=2, label=BF, color=\"green\"]\n"%(str(fact),str(fact)[2:]))
                if(fact in pairs):
                    pairs[fact].append(get_base_by_name(str(fact)[2:],components))
                elif(get_base_by_name(str(fact)[2:],components) in pairs):
                    pairs[get_base_by_name(str(fact)[2:],components)].append(fact)
                else:
                    pairs[fact]=[get_base_by_name(str(fact)[2:],components)]
                num_pairs+=1
        elif(c['type']=="agent"):
            for r in c['regions']['assertion']:
                f.write("%s -> %s [style=dotted]\n"%(c['name'],str(r)))
            for r in c['regions']['belief']:
                f.write("%s -> %s [style=dotted]\n"%(c['name'],str(r)))
        #we don't write bases since their beliefs are equated to the inputs of blocks 
        elif(c['type']!="base"):
            if(c['type']=="channel"):
                f.write("%s -> %s [label=%s_%s, color=black]\n"%(c['regions']['input'],c['regions']['output'],c['name'],c['type']))
            else:
                for i in c['regions']['input']:
                    for o in c['regions']['output']:
                        f.write("%s -> %s [label=%s_%s, color=black]\n"%(i,o,c['name'],c['type']))
            if(c['type']=="inputport" or c['type']=="outputport"):
                for i in c['regions']['input']:
                    for o in c['regions']['output']:
                        if(i in pairs):
                            pairs[i].append(o)
                        elif(o in pairs):
                            pairs[o].append(i)
                        else:
                            pairs[i]=[o]
                        num_pairs+=1
                        f.write("%s -> %s [arrowhead=none, penwidth=2, label=AB, color=\"red\"]\n"%(i,o))
            elif(c['type']=="channel"):
                if(c['regions']['input'] in pairs):
                    pairs[c['regions']['input']].append(c['regions']['output'])
                elif(c['regions']['output'] in pairs):
                    pairs[c['regions']['output']].append(c['regions']['input'])
                else:
                    pairs[c['regions']['input']]=[c['regions']['output']]
                num_pairs+=1
                f.write("%s -> %s [arrowhead=none, penwidth=2, label=AA, color=\"blue\"]\n"%(c['regions']['input'],c['regions']['output']))
    
    f.write("\n}")
    f.close()
    return {'pairs':pairs,'num_pairs':num_pairs}

def write_report(path,spec_package,risk_structure,components):
    workbook = xlsxwriter.Workbook(os.path.join(path,spec_package+"_securityAssessment.xlsx"))

    #ARCHITECTURE (HW/SW requirements) sheet
    #create png and add to 
    architecture_sheet = workbook.add_worksheet("Architecture")
    (graph,) = pydot.graph_from_dot_file(os.path.join(path,spec_package+"_model.dot"))
    graph.write_png(os.path.join(path,spec_package+"_model.png"))
    architecture_sheet.insert_image('B2', os.path.join(path,spec_package+"_model.png"))

    #WEAKNESSES sheet
    first_row=["ID","Agent","Component","Comp. Type","Weakness","Mitigation","Weight","Status","Assegnee"]

    weak_sheet = workbook.add_worksheet("Weaknesses")

    weak_sheet.set_column(1, 8, 30)
    cell_format={}
    cell_format['first_weak']=workbook.add_format({'bold': True, 'font_size': 14})
    cell_format['all_weak']=workbook.add_format({'bold': False, 'font_size': 12}) #'text_wrap': True 

    for i in range(len(first_row)):
        weak_sheet.write_string(0, i, first_row[i], cell_format['first_weak']) 
    
    weak_semantics={}
    #weak_semantics['port']={ 'po':{'weakness':"selectively drops inputs and inserts new malicious data",'mitigation':"m1"}, 'pp':{'weakness':"forwards all the inputs but crafts and inserts new malicious data",'mitigation':"m2"}, 'ppi':{'weakness':"selectively drops inputs",'mitigation':"m3"}, 'dr':{'weakness':"drops all the inputs and inserts new malicious data",'mitigation':"m4"}, 'ppb0':{'weakness':"generates new outputs even when there's no incoming data from the socket",'mitigation':"m5"}, 'ppia0':{'weakness':"drops all the incoming data",'mitigation':"m6"} }
    #weak_semantics['channel']={ 'po':{'weakness':"selectively drops inputs and inserts new malicious data",'mitigation':"m1"}, 'pp':{'weakness':"forwards all the inputs but crafts and inserts new malicious data",'mitigation':"m2"}, 'ppi':{'weakness':"selectively drops inputs",'mitigation':"m3"}, 'dr':{'weakness':"drops all the inputs and inserts new malicious data",'mitigation':"m4"}, 'ppb0':{'weakness':"generates new outputs even when there's no incoming data from the socket",'mitigation':"m5"}, 'ppia0':{'weakness':"drops all the incoming data",'mitigation':"m6"} }
    weak_semantics['weak_port']={ 'po':{'weakness':"selectively drops inputs and inserts new malicious data",'mitigation':"m1"}, 'pp':{'weakness':"forwards all the inputs but crafts and inserts new malicious data",'mitigation':"m2"}, 'ppi':{'weakness':"selectively drops inputs",'mitigation':"m3"}, 'dr':{'weakness':"drops all the inputs and inserts new malicious data",'mitigation':"m4"} }
    weak_semantics['weak_channel']={ 'po':{'weakness':"selectively drops inputs and inserts new malicious data",'mitigation':"m1"}, 'pp':{'weakness':"forwards all the inputs but crafts and inserts new malicious data",'mitigation':"m2"}, 'ppi':{'weakness':"selectively drops inputs",'mitigation':"m3"}, 'dr':{'weakness':"drops all the inputs and inserts new malicious data",'mitigation':"m4"} }
    weak_semantics['weak_out_block']={ 'po':{'weakness':"the component has a Byzantine behavior where occasionally outputs the expected output given the correct inputs. Not all the inputs are handled properly, nor all the expected outputs are always generated when correct inputs are given.",'mitigation':"m5"}, 'pp':{'weakness':"part of the expected outputs are not generated in response to the correct inputs",'mitigation':"m6"}, 'ppi':{'weakness':"the components correctly performs the expected behavior when the correct inputs are provided but is subject to input injections",'mitigation':"m7"}, 'dr':{'weakness':"the component never performs the expected behavior (e.g. physical damage)",'mitigation':"m8"} }
    weak_semantics['weak_in_block']={ 'po':{'weakness':"po",'mitigation':"m5"}, 'pp':{'weakness':"pp",'mitigation':"m6"}, 'ppi':{'weakness':"ppi",'mitigation':"m7"}, 'dr':{'weakness':"dr",'mitigation':"m8"} }

    # if R(left,right)=R(B,F) or R(F,B)
    #   in=None
    #   out=False
    #   forall c in Comp:
    #     if B is Out(c):
    #         weakness_semantics(c,R,weak_output_of_block)
    #         out=True
    #         break
    #     if B is In(c):
    #         in=c
    #   if(out==False):
    #     weakness_semantics(in,R,weak_input_of_block)
    # elif R(left,right)=R(A,B) or R(B,A)
    #   forall c in Comp:
    #      if A is In(c) and B is Out(c) or viceversa:
    #           weakness_semantics(c,R,weak_port)
    #           break
    # elif R(left,right)=R(A1,A2)
    #   forall c in Comp:
    #       if A1 is In(c) and A2 is Out(c) or viceversa:
    #           weakness_semantics(c,R,weak_channel)
    weak_id=1
    for rel,pairs_weight in risk_structure.items():
        for pair,weight in pairs_weight.items():
            left=pair[0]
            right=pair[1]
            left_type=get_base_type(pair[0])
            right_type=get_base_type(pair[1])
            weakness={'component':None,'input':None,'relation':rel,'semantics':None,'agent':None}

            if((left_type=="belief" and right_type=="assertion") or (right_type=="belief" and left_type=="assertion")): #ab
                for k,v in components.items():
                    if(v['type'] in {"inputport","outputport"}):
                        for i in v['regions']['input']:
                            for o in v['regions']['output']:
                                if((i==left and o==right) or (i==right and o==left)):
                                    weakness['component']=k
                                    weakness['relation']=rel
                                    weakness['semantics']="weak_port"
                                    break

            elif((left_type=="belief" and right_type=="fact") or (right_type=="belief" and left_type=="fact")): #bf
                comp_tmp=None
                out_comp=False
                input_tmp=None
                for k,v in components.items():
                    if(v['type'] in {"inputsocket","outputsocket","funblock"}):
                        for o in v['regions']['output']:
                            if((left_type=="belief" and o==left) or (right_type=="belief" and o==right)):
                                out_comp=True
                                weakness['component']=k
                                weakness['relation']=rel
                                weakness['semantics']="weak_out_block"
                                break
                        for i in v['regions']['input']:
                            if((left_type=="belief" and i==left) or (right_type=="belief" and i==right)):
                                comp_tmp=k
                                input_tmp=i
                if(not out_comp):
                    for c in components.values():
                        if(c['type']=="base" and c['regions']['belief']==input_tmp):
                            weakness['input']=c['name']
                            break
                    weakness['component']=comp_tmp
                    weakness['relation']=rel
                    weakness['semantics']="weak_in_block"

            elif(left_type=="assertion" and right_type=="assertion"): #aa
                for k,v in components.items():
                    if(v['type'] == "channel"):
                        if((v['regions']['input']==left and v['regions']['output']==right) or (v['regions']['input']==right and v['regions']['output']==left)):
                            weakness['component']=k
                            weakness['relation']=rel
                            weakness['semantics']="weak_channel"

            owner_tmp=None
            while(True):
                owner_tmp=components[components[weakness['component']]['owner']]
                if(owner_tmp['type']=="agent" or owner_tmp['type']=="root" ):
                    weakness['agent']=owner_tmp['name']
                    break

            weak_sheet.write(weak_id, 0, weak_id, cell_format['all_weak'])
            weak_sheet.write(weak_id, 1, weakness['agent'], cell_format['all_weak'])
            if(weakness['input']!=None):
                weak_sheet.write(weak_id, 2, components[weakness['component']]['name']+"["+weakness['input']+"]", cell_format['all_weak'])
            else:
                weak_sheet.write(weak_id, 2, components[weakness['component']]['name'], cell_format['all_weak'])
            weak_sheet.write(weak_id, 3, components[weakness['component']]['type'], cell_format['all_weak'])
            weak_sheet.write(weak_id, 4, weak_semantics[weakness['semantics']][weakness['relation']]['weakness'], cell_format['all_weak'])
            weak_sheet.write(weak_id, 5, weak_semantics[weakness['semantics']][weakness['relation']]['mitigation'], cell_format['all_weak'])
            weak_sheet.write(weak_id, 6, weight, cell_format['all_weak'])
            weak_sheet.write(weak_id, 7, "open", cell_format['all_weak'])
            weak_id+=1

    status_position=0
    for i in first_row:
        if(i!="Status"):
            status_position+=1
        else:
            break
    weak_sheet.data_validation(1,status_position,weak_id,status_position,{'validate': 'list', 'source': ['open', 'mitigated']})

    #RISK sheet
    risk_sheet = workbook.add_worksheet("Risk")

    workbook.close()

path = os.path.join("./","secra_output")
if not os.path.exists(path):
    os.mkdir(path)

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
PPi= Function('PPi', Base, Base, BoolSort())

# create list of unique regions (and subregions) of the spec
# as a (time) speedup this can be an output of create_regions_from_xmi()
print("1. Parse package %s in %s and calculate Bases"%(spec_package,xmi_filename))
components=create_regions_from_xmi(spec_package,xmi_filename)
#TODO generate a json  
f=open(os.path.join(path,spec_package+"_model.out"),"w+")
pprint.pprint(components,f)
f.close()

print("2. Calculate pairs and generate graph")
pairs_num=generate_graph(components)

print("3. Analyze graph")
f=open(os.path.join(path,spec_package+".out"),"w+")
f.write("spec: %s\n"%spec_package)
f.write("pairs of regions: %s\n"%str(pairs_num['num_pairs']))

#decompose in disconnected subgraph
#and extract cycles
#implement a DFS and detect all disconnected subgraph
#and per each one detect if they contain cycles

#DEBUG the following code is just to test cycles -- remove code below
pair_to_add=[]
for k in pairs_num['pairs'].keys():
    if(str(k)=="B31"):
        pair_to_add.append(k)
    elif(str(k)=="A23"):
        pair_to_add.append(k)

pairs_num['pairs'][pair_to_add[0]].append(pair_to_add[1])
print("****(DEBUG) MODIFIED STRUCTURE TO DEBUG CYCLE-FUN")
# DEBUG REMOVE code above

# the data structure (pairs_num['pairs']) is a 
# list of pairs implemented as an adjacence list of a directed graph
# but contains either [A,[B]] or [B[A]], not both 
found=[]
connected_nodes=[]
stack=[]
subgraphs={}
subgraphs['acycle']=[]
subgraphs['cycle']=[]
for n,adj in pairs_num['pairs'].items():
    # we should use a deque for performance
    # https://realpython.com/how-to-implement-python-stack/
    if(len(stack)!=0):
        print("ERROR")
        sys.exit(0)
    if(n not in found):
        stack.append(n)
    else:
        continue
    #print("n:",n)
    #print("stack:",stack)
    #print("found:",found)
    #print()
    cycle=False
    while(len(stack) != 0):
        current=stack.pop()
        if(current not in found):
            found.append(current)
        if(current not in connected_nodes):
            connected_nodes.append(current)
        else: 
            #print("cycle",current)
            #print(connected_nodes)
            cycle=True
        if(current in pairs_num['pairs'].keys()):
            for adj_node in pairs_num['pairs'][current]:
                stack.append(adj_node)
        #print("current:",current)
        #print("stack:",stack)
        #print("found:",found)
        #print()
    #print("cn ",connected_nodes)
    if(cycle):
        subgraphs['cycle'].append(connected_nodes)
    else:
        subgraphs['acycle'].append(connected_nodes)
    connected_nodes=[]

counter=0
#risk_structure{ relation:{pairs:weight} }
risk_structure={'po':{},'pp':{},'ppi':{},'dr':{}}

#suppose rcc5
# Cyclic and acyclic sub-graphs CG_1,...,CG_n,AG_1,...,AG_n do not affect each others.
# We can see them as independet parts of a combination. If each sub-graph had only 5 configurations
# representing a sub-part of a scenario, the number of possible scenarios would be 5^{#sub-graphs}=5^{2n}.
# When a subgraph is removed, to calculate the new number of possible scenarios 1 needs to be
# removed at the exponent (e.g. removing 1 sub-graph results in 5^{2n-1}.
# If each acyclic sub-graph has M relations of arity 5, those relations are independent (do not affect each other)
# therefore, the number of combination 5^M. With N acyclic sub-graphs, each with M relations with arity 5 we have
# 5^M^N=5^{M*N} scenarios; removing 1 relation would result in 5^{(M*N)-1} scenarios

if(subgraphs['acycle']!=[]):
    print("FOUND %d SIMPLE (ACYCLICAL) STRUCTURE(S)"%len(subgraphs['acycle']))
for s in subgraphs['acycle']:
    f.write("\nSIMPLE ACYCLIC SUBGRAPHS (Any relation in RCC5 holds and do not affect the rest of the model)\n")
    for node in s:
        if(node in pairs_num['pairs'].keys()):
            f.write("%d [%s,%s]\n"%(counter, str(node),str(pairs_num['pairs'][node])))
            for i in pairs_num['pairs'][node]:
                risk_structure['po'][(node,i)]=5
                risk_structure['pp'][(node,i)]=5
                risk_structure['pp'][(node,i)]=5
                risk_structure['dr'][(node,i)]=5
    counter+=1
print("Analysis on simple structures concluded and reported\n")

#in the case of cyclical structures we need to calculate the number of scenarios in which
# a relation appears

if(subgraphs['cycle']!=[]):
    print("FOUND %d COMPLEX (CYCLICAL) STRUCTURE(S)\n"%len(subgraphs['cycle']))

cyclic_struct_counter=1
for s in subgraphs['cycle']:
    f.write("Analyze structure %d\n"%cyclic_struct_counter)
    print("Analyze structure %d\n"%cyclic_struct_counter)

    sub_pairs_num={}
    for node in s:
        if(node in pairs_num['pairs'].keys()):
            sub_pairs_num[node]=pairs_num['pairs'][node]

    print("Add constraints on regions (for the unfolding of quantifiers)")
    regions_subregions_pairs=add_minimal_subregions(sub_pairs_num,solver)
    
    # add topology theory to solver
    print("Create Topological structure, RCC5 Theory + unfolding quantifiers")
    rcc_five(solver, regions_subregions_pairs['regions'].union(regions_subregions_pairs['subregions']), P, O, EQ, PP, PO, PPi, DR)
    print()
    
    #create a list of rcc5 relation per each pair of regions
    rcc5=[EQ,PP,PPi,PO,DR]
    itertables = []
    pairs_array=regions_subregions_pairs['pairs_array']
    for i in pairs_array:
        itertables.append(rcc5)
    
    counter=1
    counter_sat=0
    counter_unsat=0
    counter_unknown=0
    
    num_pairs=0
    for v in sub_pairs_num.values():
        num_pairs+=len(v)
    num_scenarios=5**len(itertables)
    f.write("possible scenarios: %s\n\n"%str(num_scenarios))
    #itertools creates the cartesian product on the vector of rcc5 relations
    #total_scenarios=len(list(itertools.product(*itertables)))
    avg_time=0.00000
    sum_time=0.00000
    
    # TODO save pairs and restart from that iteration
    # https://stackoverflow.com/questions/36802314/python-itertools-product-start-from-certain
    for t in itertools.product(*itertables):
        risk_tmp=[]
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
            array_scenario.append(t[i](pairs_array[i]))
            if(t[i]!=EQ):
                risk_tmp.append([str(t[i]).lower(),pairs_array[i]])

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
            if(t[i]!=EQ):
                for r in risk_tmp:
                    if(tuple(r[1]) in risk_structure[r[0]]):
                        risk_structure[r[0]][tuple(r[1])]+=1
                    else:
                        risk_structure[r[0]][tuple(r[1])]=1

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
        #This should never happen
        statistics+="\nUNKNOWN=%d"%unknown
    f.write("%s\n"%statistics)
    cyclic_struct_counter+=1

f.close()

print("Write Excel Report")
write_report(path,spec_package,risk_structure,components)
