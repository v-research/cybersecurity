import sys
import pprint
import re 
import xml.etree.ElementTree as ET

#given as inputs:
# - xmi: v-research xmi containing the whole Engineering of:
# -- the ABF-theory (of which the package name needs to be specified in abf_theory_package)
# -- the package of the cps spec (in cps_spec_name)
# -- and the scheme of the xmi (of which we support 2.1 even if we export 2.4.1 with modelio
#returns as output a structure of components as a dictionary with two entries:
# 1. components: {ID:{'name': 'sensor', 'owner': 'root', 'type': 'agent'}}
# 2. flows: {ID: [ID1, ID2, ...]}
def get_components_from_xmi(cps_spec_name,abf_theory_package="ABFTheory",schema="{http://schema.omg.org/spec/XMI/2.1}",xmi="Engineering.xmi"):
    components_flows={}
    tree = ET.parse('Engineering.xmi')
    root = tree.getroot()
    #{id:{name,type}} for agents, ports, and functional blocks
    components={}
    #adjacency list
    #{id1:[id2]} for information flows (id1->id2)
    #{id1:[id2, id3]} for information flows (id1->id2 and id1->id3)
    flows={}
    ID={}
    for child in root:
        if(child.tag == "packagedElement"):
            if(child.attrib[schema+'type'] == "uml:Package" and child.attrib['name'] == abf_theory_package):
                for elem in child:
                    if(elem.attrib['name'] == "Base"):
                        ID[elem.attrib[schema+'id']]='Base'
                        break
            elif(child.attrib[schema+'type'] == "uml:Class"):
                if(child.attrib['name'] == "InputPort"):
                    ID[child.attrib[schema+'id']]='InputPort'
                elif(child.attrib['name'] == "OutputPort"):
                    ID[child.attrib[schema+'id']]='OutputPort'
                elif(child.attrib['name'] == "FunctionalBlock"):
                    ID[child.attrib[schema+'id']]='FunctionalBlock'
    
            #this is just a speedup but we need to increase this is we add support for other attributes 
            if(len(ID)==4):
                break
    
    for child in root:
            if(child.tag == "packagedElement" and child.attrib['name'] == cps_spec_name):
                for innerchild in child:
                    #print(innerchild.tag, innerchild.attrib)
                    #find agents as Nodes in deployment diagram
                    if(innerchild.attrib[schema+'type'] == "uml:Node"):
                        #print(innerchild.tag, innerchild.attrib)
                        components[innerchild.attrib[schema+'id']]={'name':innerchild.attrib['name']}
                        components[innerchild.attrib[schema+'id']]['type']='agent'
                        components[innerchild.attrib[schema+'id']]['owner']='root'
                        for attribute in innerchild:
                            #print(attribute.tag, attribute.attrib)
                            #print(attribute.attrib[schema+'type']) 
                            if(attribute.attrib[schema+'type'] == "uml:Port"):
                                components[attribute.attrib[schema+'id']]={'name':attribute.attrib['name']}
                                if(ID[attribute.attrib['type']]=="InputPort"):
                                    components[attribute.attrib[schema+'id']]['type']='inputport'
                                elif(ID[attribute.attrib['type']]=="OutputPort"):
                                    components[attribute.attrib[schema+'id']]['type']='outputport'
                                components[attribute.attrib[schema+'id']]['owner']=innerchild.attrib['name']
                            elif(attribute.attrib[schema+'type'] == "uml:Property"):
                                components[attribute.attrib[schema+'id']]={'name':attribute.attrib['name']}
                                components[attribute.attrib[schema+'id']]['owner']=innerchild.attrib['name']
                                if(ID[attribute.attrib['type']]=="InputPort"):
                                    components[attribute.attrib[schema+'id']]['type']='inputsocket'
                                elif(ID[attribute.attrib['type']]=="OutputPort"):
                                    components[attribute.attrib[schema+'id']]['type']='outputsocket'
                                elif(ID[attribute.attrib['type']]=="FunctionalBlock"):
                                    components[attribute.attrib[schema+'id']]['type']='funblock'
                                elif(ID[attribute.attrib['type']]=="Base"):
                                    components[attribute.attrib[schema+'id']]['type']='base'
                                else:
                                    print("DEBUG Attribute not supported")
                                    print("DEBUG name: ",attribute.attrib['name'])
                                    print("DEBUG id: ",attribute.attrib[schema+'id'])
                    elif(innerchild.attrib[schema+'type'] == "uml:InformationFlow"):
                        if(innerchild.attrib['informationSource'] in flows):
                            flows[innerchild.attrib['informationSource']].append(innerchild.attrib['informationTarget'])
                        else:
                            flows[innerchild.attrib['informationSource']]=[innerchild.attrib['informationTarget']]
    
    
    #we createa channel per each flow between ports
    for f1k,f1v in flows.items():
        if(components[f1k]['type']=="outputport"):
            for target in f1v:
                if(components[target]['type']=="inputport"):
                    components[f1k+target]={'name':components[f1k]['name']+"2"+components[target]['name'],'owner':"root",'type':"channel"}
    
    #we create a "fake flow" from port-socket 
    #for each port there must be a socket, the opposite may not be true
    #we could also merge based on name
    for c1k,c1v in components.items():
        if(c1v['type']=="inputport" or c1v['type']=="outputport"):
            for c2k,c2v in components.items():
                if(c2v['type']=="inputsocket" or c2v['type']=="outputsocket"):
                    if(c1v['name'] == c2v['name']):
                        if(c1v['type']=="inputport"):
                            #port -> socket
                            if(c1k in flows):
                                flows[c1k].append(c2k)
                            else:
                                flows[c1k]=[c2k]
                        elif(c1v['type']=="outputport"):
                            #socket -> port
                            if(c2k in flows):
                                flows[c2k].append(c1k)
                            else:
                                flows[c2k]=[c1k]

    components_flows['components']=components
    components_flows['flows']=flows
    return components_flows

def dot(cps_spec_name, components, flows):
    f=open(cps_spec_name+".dot","w+")
    f.write("digraph %s {"%re.sub('[^A-Za-z0-9]+', '', cps_spec_name))
    f.write("\n\tnode [shape=record];")
    for k,v in components.items():
        if(v['type']=="inputport" or v['type']=="outputport"):
            f.write("\n\t %s_%s [style=filled]"%(v['name'],v['type']))
    for k,v in components.items():
        if(v['type']=="agent"):
            f.write("\n\tsubgraph cluster_%s {\n\t\tlabel=\"%s\";\n\t\tlabeljust=\"l\""%(v['name'],v['name']))
            for k2,v2 in components.items():
                if(v2['owner']==v['name'] and v2['type']!="inputport" and v2['type']!="outputport"):
                    f.write("\n\t\t%s_%s"%(v2['name'],v2['type']))
                    if(v2['type']=="base"):
                        f.write(" [style=dashed]")
                    f.write(";")
            f.write("\n\t}")

    for f1,f2 in flows.items():
        for e in f2:
            if(components[f1]['type']=="outputport" and components[e]['type']=="inputport"):
                f.write("\n%s_%s -> %s_%s"%(components[f1]['name'],components[f1]['type'],components[e]['name'],components[e]['type']))
                f.write(" [penwidth=5, arrowhead=none];")
            else:
                f.write("\n%s_%s -> %s_%s"%(components[f1]['name'],components[f1]['type'],components[e]['name'],components[e]['type']))
                f.write(" [color=gray40];")
    f.write(("\n}"))
    f.close()


#TODO
# generate Regions
# change IDs in components structure (but keep a map?) so that we can generate regions with a decent name (e.g. A_1, B_2 etc)
# foreach agent a
#   create(A_a and B_a)
#   foreach funblock (we can fogive about sockets? maybe not) f in a
#     create(B_fi and B_fo) subsets of B_a
#   foreach channel that has a port p in a
#     create(A_p) subset of A_a

def test_this_file():
    spec="UC1-CPS"
    components_flows=get_components_from_xmi(cps_spec_name=spec)
    components=components_flows['components']
    flows=components_flows['flows']
    
    pp=pprint.PrettyPrinter(indent=0)
    pp.pprint(components)
    pp.pprint(flows)
    
    dot(spec, components, flows)

#if __name__ == "__main__":
#    test_this_file()
