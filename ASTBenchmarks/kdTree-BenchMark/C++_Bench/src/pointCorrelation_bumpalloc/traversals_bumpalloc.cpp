//
//  traversals_unpacked.cpp
//  PackedTrees
//
//  Created by lsakka on 10/27/16.
//  Copyright © 2016 lsakka. All rights reserved.
//

#include <stdio.h>
#include "tree_bumpalloc.h"

void   printUnpackedTree(Tree_Node * node){
    //print Tag
    
    
    cout<<" ,tag:"<<node->tag<<endl;
    
    if(node->tag==LEAF_TAG){
        cout<<"x:"<<node->leafData.x_val<<" ,y:"<<node->leafData.y_val<<endl;
    }
    else{
        cout<<" ,splitAxis:"<<node->innerData.splitAxis<<" ,splitLocation:"<<node->innerData.splitLoc<<endl;
        cout<<" ,min_x:"<<node->innerData.min_x;
        cout<<" ,max_x:"<<node->innerData.max_x<<endl;
        cout<<" ,min_y:"<<node->innerData.min_y;
        cout<<" ,max_y:"<<node->innerData.max_y<<endl;
        
        printUnpackedTree(node->innerData.leftChild);
        printUnpackedTree(node->innerData.rightChild);
    }
    
}

void performPointCorr_OnTree(Point & p,Tree_Node * node ,float rad){
    
    if(node->tag == LEAF_TAG){
        float d = 0;
        
        d +=(p.x_val - node->leafData.x_val) *(p.x_val - node->leafData.x_val);
        d +=(p.y_val - node->leafData.y_val) *(p.y_val - node->leafData.y_val);
        
        if(sqrt(d) < rad){
            node->leafData.corr++;
#ifdef TEST
            counter++;
#endif
        }
    }else {
        
        float sum    = 0.0;
        float boxsum = 0.0;
        float center_x  =
        ( node->innerData.max_x + node->innerData.min_x )/ 2;
        float boxdist_x  =
        ( node->innerData.max_x - node->innerData.min_x)/ 2;
        
        float dist_x    = p.x_val - center_x;
        sum    += dist_x * dist_x;
        boxsum += boxdist_x * boxdist_x;
        //do same thing for y
        
        float center_y  =
        ( node->innerData.max_y + node->innerData.min_y )/ 2;
        
        float boxdist_y  =
        ( node->innerData.max_y - node->innerData.min_y)/ 2;
        
        
        float dist_y    = p.y_val - center_y;
        sum    += dist_y * dist_y;
        boxsum += boxdist_y * boxdist_y;
        
        bool canCorrelate = sqrt(sum) - sqrt(boxsum) < rad;
        
        if(!(canCorrelate)){
            return ;
            
            
        }else{
            //call left
            performPointCorr_OnTree(p, node->innerData.leftChild, rad);
            
            //call right child
            performPointCorr_OnTree(p,  node->innerData.rightChild, rad);
            
            
        }
        
        
    }
    
}

int performPointCorr_IntOut(Point & p,Tree_Node * node ,float rad){
    
    if(node->tag == LEAF_TAG){
        float d = 0;
        
        d +=(p.x_val - node->leafData.x_val) *(p.x_val - node->leafData.x_val);
        d +=(p.y_val - node->leafData.y_val) *(p.y_val - node->leafData.y_val);
        
        if(sqrt(d) < rad){
            //node->leafData.corr++;
            return 1;
        }
        return 0;
    }else {
        
        float sum    = 0.0;
        float boxsum = 0.0;
        float center_x  =( node->innerData.max_x + node->innerData.min_x )/ 2;
        float boxdist_x  =( node->innerData.max_x - node->innerData.min_x)/ 2;
        float dist_x    = p.x_val - center_x;
        float center_y  =( node->innerData.max_y + node->innerData.min_y )/ 2;
        float boxdist_y  =( node->innerData.max_y - node->innerData.min_y)/ 2;
        float dist_y    = p.y_val - center_y;
        
        sum    += dist_x * dist_x;
        boxsum += boxdist_x * boxdist_x;
        
        sum    += dist_y * dist_y;
        boxsum += boxdist_y * boxdist_y;
        
        bool canCorrelate = sqrt(sum) - sqrt(boxsum) < rad;
        
        if(!(canCorrelate)){
            return 0;
            
        }else{
            //call left
            return  performPointCorr_IntOut(p, node->innerData.leftChild, rad)+  performPointCorr_IntOut(p,  node->innerData.rightChild, rad);
            
        }
    }
}

Tree_Node *   copyNodes(Tree_Node * node){
    
    Tree_Node * nodeRet=(Tree_Node *)(BumpAllocator::alloc(sizeof(Tree_Node)));
    
#ifdef TEST
    nodeCount_test++;
#endif
    
    if(node->tag==LEAF_TAG)
    {
        nodeRet->tag=LEAF_TAG;
        nodeRet->leafData=node->leafData;
        
    }else if(node->tag==INNER_TAG){
        nodeRet->tag=INNER_TAG;
        nodeRet->innerData.max_x=node->innerData.max_x;
        nodeRet->innerData.min_x=node->innerData.min_x;
        nodeRet->innerData.max_y=node->innerData.max_y;
        nodeRet->innerData.min_y=node->innerData.min_y;
        nodeRet->innerData.splitAxis=node->innerData.splitAxis;
        nodeRet->innerData.splitLoc=node->innerData.splitLoc;
        
        nodeRet->innerData.leftChild=copyNodes(node->innerData.leftChild);
        nodeRet->innerData.rightChild=copyNodes(node->innerData.rightChild);
    }
    return nodeRet;
}

Tree_Node *   performPointCorr_TreeOut(Point & p,Tree_Node * node ,float rad){
    
    Tree_Node * nodeOut=(Tree_Node *)(BumpAllocator::alloc(sizeof(Tree_Node)));
    
#ifdef TEST
    nodeCount_test++;
#endif
    nodeOut->tag=node->tag;
    
    if(node->tag == LEAF_TAG){
        float d = 0;
        
        //copy unchanged data
        nodeOut->leafData.x_val=node->leafData.x_val;
        nodeOut->leafData.y_val=node->leafData.y_val;
        
        //set the counter
        d +=(p.x_val - node->leafData.x_val) *(p.x_val - node->leafData.x_val);
        d +=(p.y_val - node->leafData.y_val) *(p.y_val - node->leafData.y_val);
        
        if(sqrt(d) < rad){
            nodeOut->leafData.corr=node->leafData.corr+1;
#ifdef TEST
            counter2++;
#endif
            
        }
        else{
            nodeOut->leafData.corr=node->leafData.corr;
        }
        return nodeOut;
    }else {
        //copy  data
        nodeOut->innerData.max_x=node->innerData.max_x;
        nodeOut->innerData.min_x=node->innerData.min_x;
        nodeOut->innerData.max_y=node->innerData.max_y;
        nodeOut->innerData.min_y=node->innerData.min_y;
        nodeOut->innerData.splitAxis=node->innerData.splitAxis;
        nodeOut->innerData.splitLoc=node->innerData.splitLoc;
        
        float sum    = 0.0;
        float boxsum = 0.0;
        float center_x  = ( node->innerData.max_x + node->innerData.min_x )/ 2;
        float boxdist_x  =( node->innerData.max_x - node->innerData.min_x)/ 2;
        float dist_x    = p.x_val - center_x;
        float center_y  =( node->innerData.max_y + node->innerData.min_y )/ 2;
        float boxdist_y  =( node->innerData.max_y - node->innerData.min_y)/ 2;
        float dist_y    = p.y_val - center_y;
        
        sum    += dist_x * dist_x;
        boxsum += boxdist_x * boxdist_x;
        sum    += dist_y * dist_y;
        boxsum += boxdist_y * boxdist_y;
        
        bool canCorrelate = sqrt(sum) - sqrt(boxsum) < rad;
        
        if(!(canCorrelate)){
            
            nodeOut->innerData.leftChild=copyNodes(node->innerData.leftChild);
            nodeOut->innerData.rightChild=copyNodes(node->innerData.rightChild);
            
        }else{
            nodeOut->innerData.leftChild  =  performPointCorr_TreeOut(p, node->innerData.leftChild, rad);
            nodeOut->innerData.leftChild =  performPointCorr_TreeOut(p,  node->innerData.rightChild, rad);
            
        }
        return nodeOut;
    }
}
