cs565 max-flow/min-cut theorem
============

Formalize a graph network with edges labelled with their capacity.
Prove max-flow/min-cut theorem of Graph Theory.

####Log:
#####04/07/2014 
Defined the vertex, list and graph structure. 

#####04/21/2014 
No significative advance before. Readjusted everything.
Modified definition of principals structures (vertex, graph). Graph is defined as a list of vertex, where edge are represented as adjacence list. Added principal fixpoints headers, graph properties.

#####04/23/2014 
Completed the fixpoints related to Graph definition.

#####04/25/2014 
Added GraphExample in order to test fixpoints and properties using a example graph of 4 vertex.  Added attrib. flow to the Graph structure as a new attrib in vertex definition (VerName * Weight * Flow). Adjusted definitions according to changes made.

#####04/30/2014 
Changes list fixpoint from Prop to bool. Did some adjustment in Graph Properties and lemma.

####TODO:
Prove theorems: exists_max_flox and flow_conservation_path.
