import pprint
import re 
import xml.etree.ElementTree as ET
tree = ET.parse('Engineering.xmi')
root = tree.getroot()

cps_spec_name="UC1-CPS"

#{id:{name,type}} for agents, ports, and functional blocks
components={}
#{id1:id2} for information flows (id---message--->id)
flows={}

#this dictionary is only used to create
#a "fake flow" from outer-port to inner-port (socket)
#we could also merge based on name
ports={}

ID={}
schema="{http://schema.omg.org/spec/XMI/2.1}"

for child in root:
    if(len(ID)==3):
        break
    if(child.tag == "packagedElement"):
        if(child.attrib[schema+'type'] == "uml:Class"):
            if(child.attrib['name'] == "InputPort"):
                ID[child.attrib[schema+'id']]='InputPort'
            if(child.attrib['name'] == "OutputPort"):
                ID[child.attrib[schema+'id']]='OutputPort'
            if(child.attrib['name'] == "FunctionalBlock"):
                ID[child.attrib[schema+'id']]='FunctionalBlock'

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
                        if(attribute.attrib[schema+'type'] == "uml:Port"):
                            ports[attribute.attrib['name']]=attribute.attrib[schema+'id']
                            components[attribute.attrib[schema+'id']]={'name':attribute.attrib['name']}
                            components[attribute.attrib[schema+'id']]['type']='port'
                            components[attribute.attrib[schema+'id']]['owner']=innerchild.attrib['name']
                        if(attribute.attrib[schema+'type'] == "uml:Property"):
                            components[attribute.attrib[schema+'id']]={'name':attribute.attrib['name']}
                            components[attribute.attrib[schema+'id']]['owner']=innerchild.attrib['name']
                            if(ID[attribute.attrib['type']]=="InputPort" or ID[attribute.attrib['type']]=="OutputPort"):
                                components[attribute.attrib[schema+'id']]['type']='socket'
                                #get the name of the Port in the deplyment diagram with the same name of this socket
                                for k,v in ports.items():
                                    if(k==attribute.attrib['name']):
                                        #check if it's an input or output port to add the correct direction of the flow
                                        if(ID[attribute.attrib['type']]=="InputPort"):
                                            flows[v]=attribute.attrib[schema+'id']
                                        elif(ID[attribute.attrib['type']]=="OutputPort"):
                                            flows[attribute.attrib[schema+'id']]=v
                                        else:
                                            print("ERROR")
                                        break
                            elif(ID[attribute.attrib['type']]=="FunctionalBlock"):
                                components[attribute.attrib[schema+'id']]['type']='funblock'
                elif(innerchild.attrib[schema+'type'] == "uml:InformationFlow"):
                    flows[innerchild.attrib['informationSource']]=innerchild.attrib['informationTarget']


pp=pprint.PrettyPrinter(indent=0)
pp.pprint(components)

def dot(cps_spec_name, components, flows):
    f=open(cps_spec_name+".dot","w+")
    f.write(("digraph %s {"%re.sub('[^A-Za-z0-9]+', '', cps_spec_name)))
    f.write(("\tnode [shape=record];"))
    for k,v in components.items():
        if(v['type']=="agent"):
            f.write(("\tsubgraph cluster_%s {\n\t\tlabel=\"%s\";\n\t\tlabeljust=\"l\""%(v['name'],v['name'])))
            for k2,v2 in components.items():
                if(v2['owner']==v['name'] and v2['type']!="port"):
                    f.write(("\t\t%s_%s;"%(v2['name'],v2['type'])))
            f.write(("\t}"))

    for f1,f2 in flows.items():
        f.write(("%s_%s -> %s_%s;"%(components[f1]['name'],components[f1]['type'],components[f2]['name'],components[f2]['type'])))
    f.write(("}"))
    f.close()

dot(cps_spec_name, components, flows)
