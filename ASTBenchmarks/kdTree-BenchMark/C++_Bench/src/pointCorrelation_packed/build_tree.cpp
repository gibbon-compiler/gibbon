//
//  tree_packed.c
//  PackedTrees
//
//  Created by lsakka on 10/25/16.
//  Copyright © 2016 lsakka. All rights reserved.
//

#include "tree_packed.h"



void readPoint(FILE *in, Point & p){
    int dummy;
    if(fscanf(in, "%d", &dummy) != 1) {
        fprintf(stderr, "Input file not large enough.\n");
        exit(1);
    }
    
    if(fscanf(in, "%f", &p.x_val) != 1) {
        fprintf(stderr, "Input file not large enough.\n");
        exit(1);
    }
    if(fscanf(in, "%f", &p.y_val) != 1) {
        fprintf(stderr, "Input file not large enough.\n");
        exit(1);
    }
    
}

void readInput(int argc, char **argv,Point * & data , float & rad, int & npoints, Varient & mode){
    
    if(argc != 4 && argc != 3) {
        fprintf(stderr, "usage: pointcorr <DIM> <rad> <npoints> [input_file]\n");
        exit(1);
    }
    
    
    rad = atof(argv[1]);
    
    npoints = atol(argv[2]);
    
    if(npoints <= 0) {
        fprintf(stderr, "Not enough points.\n");
        exit(1);
    }
    
    data = new Point[npoints];
    string varient=(argv[3]);
    if(varient.compare("updatetree")==0)
        mode=Varient::updateTree;
    else  if(varient.compare("treeout")==0)
        mode=Varient::treeOut;
    else  if(varient.compare("intout")==0)
        mode=Varient::intOut;
    
    
    
    srand(0);
    for(int i = 0; i < npoints; i++) {
        data[i].x_val= (float)rand() / RAND_MAX;
        data[i].y_val= (float)rand() / RAND_MAX;
        
    }
    
}


float max(float a, float b){
    return a > b ? a : b;
}

float min(float a, float b){
    return a < b ? a : b;
}

long long treeSize(long long n,bool withIndirection){
    if(withIndirection)
        return  (sizeof(Node_Leaf))* n +  (sizeof(Node_Inner_Indirection))*n + (2*n)*sizeof(char );

    else
        return (sizeof(Node_Leaf))* n +  (sizeof(Node_Inner_NoIndirection))*n + (2*n)*sizeof(char );
}
int comparePointX(const void *a, const void *b){
    if(((Point *)a)->x_val < ((Point *)b)->x_val)
        return -1;
    else if(((Point *)a)->x_val> ((Point *)b)->x_val)
        return 1;
    else
        return 0;
}

int comparePointY(const void *a, const void *b){
    if(((Point *)a)->y_val < ((Point *)b)->y_val)
        return -1;
    else if(((Point *)a)->y_val > ((Point *)b)->y_val)
        return 1;
    else
        return 0;
}

//return the index of the last created leaf node
void buildTreeRec_WithIndirection(int startIndx ,int endIndx ,Point * data ,char * &cur ,int depth  ){
    
    int size = endIndx - startIndx + 1;
    int mid  = (startIndx + endIndx) / 2;
    
    //leaf node
    if (size ==1) {
        
        * ((char*)cur)=LEAF_TAG;
        cur +=sizeof(char);
        
        //set x val
        *((float*)cur) = data[startIndx].x_val;
        cur += sizeof(float);
        
        //set y val
        * ((float*)cur)=data[endIndx].y_val;
        cur += sizeof(float);
        
        //skip the output (// do we need to create a new tree ? just for this feild !!)
        cur +=sizeof(int);
        return ;
    }
    
    //inner Node
    
    //this implementation has some derefernecing , not sure how much geeting rid of them will is better
    //since we are intereted in the traversal performance not the built its ok for now
    else if(size>1){
        nodeCount_INNER++;
        * ((char*)cur)=INNER_TAG;
        cur +=sizeof(char);
        
        
        //we can do it with out innerData by tracking cur step like the leaf , mm shal we?
        Node_Inner_Indirection * node= (Node_Inner_Indirection *)cur;
        //splitAxis
        node->splitAxis= (depth%2 == 0);
        //cur_dat-> +=sizeof(bool);
        
        //splitLoc
        //Todo : no need to resort each time! still this is not part of what we are trying to optimize now (rather than restoring keep two sorted arrays (x, y))
        
        if(depth%2==0){
            qsort(&data[startIndx], size, sizeof(Point), comparePointX);
            node->splitLoc=data[mid].x_val;
            
        }
        else{
            qsort(&data[startIndx], size, sizeof(Point), comparePointY);
            node->splitLoc = data[mid].y_val;
            
        }
        
        cur += sizeof(Node_Inner_Indirection);
        
        char * leftChild = cur;
        
        buildTreeRec_WithIndirection(startIndx, mid, data, cur, depth+1);
        
        node->RightChild=cur;
        
        buildTreeRec_WithIndirection(mid+1, endIndx, data, cur, depth+1);
        
        
        
        //any way to write these in a better way !
        int dist=1+sizeof(float);
        if(*leftChild==LEAF_TAG){
            if(* node->RightChild==LEAF_TAG){
                node->max_x=max(*(float *)(leftChild+1),*(float *)(node->RightChild+1));
                node->min_x=min(*(float *)(leftChild+1),*(float *)(node->RightChild+1));
                node->max_y=max(*(float *)(leftChild+1+sizeof(float)),*(float *)(node->RightChild+dist));
                node->min_y=min(*(float *)(leftChild+dist),*(float *)(node->RightChild+dist));
                
            }else{
                node->max_x=max(*(float *)(leftChild+1),((Node_Inner_Indirection*) (node->RightChild+1))->max_x);
                node->min_x=min(*(float *)(leftChild+1),((Node_Inner_Indirection*) (node->RightChild+1))->min_x);
                node->max_y=max(*(float *)(leftChild+dist),((Node_Inner_Indirection*) (node->RightChild+1))->max_y);
                node->min_y=min(*(float *)(leftChild+dist),((Node_Inner_Indirection*) (node->RightChild+1))->min_y);
                
            }
        }else{
            if(* node->RightChild==LEAF_TAG){
                node->max_x=max(((Node_Inner_Indirection*) (leftChild+1))->max_x,*(float *)(node->RightChild+1));
                node->min_x=min(((Node_Inner_Indirection*) (leftChild+1))->min_x,*(float *)(node->RightChild+1));
                node->max_y=max(((Node_Inner_Indirection*) (leftChild+1))->max_y,*(float *)(node->RightChild+dist));
                node->min_y=min(((Node_Inner_Indirection*) (leftChild+1))->min_y,*(float *)(node->RightChild+dist));
                
            }else{
                node->max_x=max(((Node_Inner_Indirection*) (leftChild+1))->max_x,((Node_Inner_Indirection*) (node->RightChild+1))->max_x);
                node->min_x=min(((Node_Inner_Indirection*) (leftChild+1))->min_x,((Node_Inner_Indirection*) (node->RightChild+1))->min_x);
                node->max_y=max(((Node_Inner_Indirection *) (leftChild+1))->max_y,((Node_Inner_Indirection*) (node->RightChild+1))->max_y);
                node->min_y=min(((Node_Inner_Indirection*) (leftChild+1))->min_y,((Node_Inner_Indirection*) (node->RightChild+1))->min_y);
            }
        }
    }
    
    
}

void buildTreeRec_NoIndirection(int startIndx ,int endIndx ,Point * data ,char * &cur ,int depth  ){
    
    int size = endIndx - startIndx + 1;
    int mid  = (startIndx + endIndx) / 2;
    
    //leaf node
    if (size ==1) {
        
        * ((char*)cur)=LEAF_TAG;
        cur +=sizeof(char);
        
        //set x val
        *((float*)cur) = data[startIndx].x_val;
        cur += sizeof(float);
        
        //set y val
        * ((float*)cur)=data[endIndx].y_val;
        cur += sizeof(float);
        
        //skip the output (// do we need to create a new tree ? just for this feild !!)
        cur +=sizeof(int);
        return ;
    }
    
    //inner Node
    
    //this implementation has some derefernecing , not sure how much geeting rid of them will is better
    //since we are intereted in the traversal performance not the built its ok for now
    else if(size>1){
        nodeCount_INNER++;

        * ((char*)cur)=INNER_TAG;
        cur +=sizeof(char);
        
        
        //we can do it with out innerData by tracking cur step like the leaf , mm shal we?
        Node_Inner_NoIndirection * innerData= (Node_Inner_NoIndirection *)cur;
        //splitAxis
        innerData->splitAxis= (depth%2 == 0);
        //cur_dat-> +=sizeof(bool);
        
        //splitLoc
        //Todo : no need to resort each time! still this is not part of what we are trying to optimize now (rather than restoring keep two sorted arrays (x, y))
        
        if(depth%2==0){
            qsort(&data[startIndx], size, sizeof(Point), comparePointX);
            innerData->splitLoc=data[mid].x_val;
            
        }
        else{
            qsort(&data[startIndx], size, sizeof(Point), comparePointY);
            innerData->splitLoc = data[mid].y_val;
            
        }
        
        cur += sizeof(Node_Inner_NoIndirection);
        
        char * leftChild = cur;
        
        buildTreeRec_NoIndirection(startIndx, mid, data, cur, depth+1);
        
        char * rightChildTag =cur;
        
        buildTreeRec_NoIndirection(mid+1, endIndx, data, cur, depth+1);
        
        
        
        //any way to write these in a better way !
        int dist=+1+sizeof(float);
        if(*leftChild==LEAF_TAG){
            if(* rightChildTag==LEAF_TAG){
                innerData->max_x=max(*(float *)(leftChild+1),*(float *)(rightChildTag+1));
                innerData->min_x=min(*(float *)(leftChild+1),*(float *)(rightChildTag+1));
                innerData->max_y=max(*(float *)(leftChild+1+sizeof(float)),*(float *)(rightChildTag+dist));
                innerData->min_y=min(*(float *)(leftChild+dist),*(float *)(rightChildTag+dist));
                
            }else{
                innerData->max_x=max(*(float *)(leftChild+1),((Node_Inner_NoIndirection*) (rightChildTag+1))->max_x);
                innerData->min_x=min(*(float *)(leftChild+1),((Node_Inner_NoIndirection*) (rightChildTag+1))->min_x);
                innerData->max_y=max(*(float *)(leftChild+dist),((Node_Inner_NoIndirection*) (rightChildTag+1))->max_y);
                innerData->min_y=min(*(float *)(leftChild+dist),((Node_Inner_NoIndirection*) (rightChildTag+1))->min_y);
                
            }
        }else{
            if(* rightChildTag==LEAF_TAG){
                innerData->max_x=max(((Node_Inner_NoIndirection*) (leftChild+1))->max_x,*(float *)(rightChildTag+1));
                innerData->min_x=min(((Node_Inner_NoIndirection*) (leftChild+1))->min_x,*(float *)(rightChildTag+1));
                innerData->max_y=max(((Node_Inner_NoIndirection*) (leftChild+1))->max_y,*(float *)(rightChildTag+dist));
                innerData->min_y=min(((Node_Inner_NoIndirection*) (leftChild+1))->min_y,*(float *)(rightChildTag+dist));
                
            }else{
                innerData->max_x=max(((Node_Inner_NoIndirection*) (leftChild+1))->max_x,((Node_Inner_NoIndirection*) (rightChildTag+1))->max_x);
                innerData->min_x=min(((Node_Inner_NoIndirection*) (leftChild+1))->min_x,((Node_Inner_NoIndirection*) (rightChildTag+1))->min_x);
                innerData->max_y=max(((Node_Inner_NoIndirection*) (leftChild+1))->max_y,((Node_Inner_NoIndirection*) (rightChildTag+1))->max_y);
                innerData->min_y=min(((Node_Inner_NoIndirection*) (leftChild+1))->min_y,((Node_Inner_NoIndirection*) (rightChildTag+1))->min_y);
            }
        }
    }
    
    
}

char *  buildTree(int n , Point * data ,bool withIndirection){

    //reserve the memory layout
    long long bytes = treeSize(n,withIndirection);
    char * buf = (char*) malloc(bytes);
    char * root=buf;
    if(withIndirection)
        buildTreeRec_WithIndirection(0, n-1, data, buf, 0);
    else
        buildTreeRec_NoIndirection(0, n-1, data, buf, 0);

    return root;
    
}



