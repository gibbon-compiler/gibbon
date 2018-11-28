//
//  traversals_packed.c
//  PackedTrees
//
//  Created by lsakka on 10/26/16.
//  Copyright © 2016 lsakka. All rights reserved.
//

#include <iostream>
#include "tree_packed.h"
#include <cassert>
using  namespace std;



char *  printPackedTree(char * & cur){
    //print Tag
    
    cout<<"address:"<<(void * )cur;
    cout<<" ,tag:"<<*(char*) (cur)<<endl;
    if(*((char*) (cur))==LEAF_TAG){
        cur +=sizeof(char);
        struct Node_Leaf * leaf=(struct Node_Leaf*) (cur);
        cout<<"x:"<<leaf->x_val<<" ,y:"<<leaf->y_val<<endl;
        cur+=sizeof(Node_Leaf);
        return cur;
    }
    else{
        cur +=sizeof(char);
        struct Node_Inner_NoIndirection * inner=(struct Node_Inner_NoIndirection*) (cur);
        cout<<" ,splitAxis:"<<inner->splitAxis<<" ,splitLocation:"<<inner->splitLoc<<endl;
        cout<<" ,min_x:"<<inner->min_x;
        cout<<" ,max_x:"<<inner->max_x<<endl;
        cout<<" ,min_y:"<<inner->min_y;
        cout<<" ,max_y:"<<inner->max_y<<endl;
        //cout<<" ,right child address:"<<(void * )inner->RightChild<<endl;;
        cur+=sizeof(Node_Inner_NoIndirection);
        
        char * rightChild=printPackedTree(cur);
        //assert(rightChild==inner->RightChild && "error in right child address in the built tree\n");
        return printPackedTree(rightChild);
    }
    
}
void performPointCorr_treeOut_rec(Point & p,char * & cur,char * & curOut,float rad);

bool performPointCorr_OnTree(Point & p,char * & cur,float rad){
    
    if(*cur == LEAF_TAG){
        
        float d = 0;
        float leaf_x = *((float *)(cur+sizeof(char))) ;
        float  leaf_y = *((float *)(cur+sizeof(char)+sizeof(float)) );
        
        d +=(p.x_val - leaf_x) *(p.x_val - leaf_x);
        d +=(p.y_val - leaf_y) *(p.y_val - leaf_y);
        
        if(sqrt(d) < rad){
            *(int * )(cur+sizeof(char)+sizeof(float)+sizeof(float))=   *(int * )(cur+sizeof(char)+sizeof(float)+sizeof(float))+1;
#ifdef TEST
            counter++;
#endif
        }
        cur += sizeof(char)+sizeof(float)+sizeof(float)+sizeof(int);
        return true;
        
    }else {

        double sum=0;
        double boxsum=0;
        //well the performance be effected if at this point
        //cur is casted to pointer of Node_Inner and members where accessed using ->?? should try it!
        float center_x  =( (*(float*) (cur+sizeof(char)+sizeof(bool)+sizeof(float))) +
                          *(float*)( cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)) )/ 2;
        
        float boxdist_x  =( -(*(float*)( cur+sizeof(char)+sizeof(bool)+sizeof(float))) +
                           *(float*)( cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float))  )/ 2;
        
        float dist_x    = p.x_val - center_x;
        sum    += dist_x * dist_x;
        boxsum += boxdist_x * boxdist_x;
        
        float center_y  =( (*(float*) (cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float))) +
                          *(float*)(cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)))/ 2;
        float boxdist_y  =( -(*(float*) (cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float))) +
                           *(float*)(cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)) )/ 2;
        
        float dist_y    = p.y_val - center_y;
        sum    += dist_y * dist_y;
        boxsum += boxdist_y * boxdist_y;
        
        bool canCorrelate = sqrt(sum) - sqrt(boxsum) < rad;
        
        if(!(canCorrelate)){
            return false ;
            
        }else{
            //call left
            cur    += sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float);

            char * pointerToRightchild=cur;
            cur+=sizeof(char * );
            bool nextIsRight =performPointCorr_OnTree(p, cur, rad);
            
            if(!nextIsRight){
                cur=(*(char * *)pointerToRightchild);
            }
            return performPointCorr_OnTree(p,cur , rad);
        }
    }
}


pair<int ,bool> performPointCorr_IntOut(Point & p,char * & cur,float rad){
    
    if(*cur == LEAF_TAG){
        //cur++;
        float d = 0;
        float leaf_x = *((float *)(cur+sizeof(char))) ;
        // cur += sizeof(float);
        float  leaf_y = *((float *)(cur+sizeof(char)+sizeof(float)) );
        //  cur += sizeof(float);
        
        d +=(p.x_val - leaf_x) *(p.x_val - leaf_x);
        d +=(p.y_val - leaf_y) *(p.y_val - leaf_y);
        
        int ret=0;
        if(sqrt(d) < rad){
            //   (*(int * )cur)++;
            ret=1;
        }
        cur += sizeof(char)+sizeof(float)+sizeof(float)+sizeof(int);
        return make_pair(ret, true) ;
        
    }else {
        //cur++;
        double sum=0;
        double boxsum=0;
        float center_x  =( (*(float*) (cur+sizeof(char)+sizeof(bool)+sizeof(float))) +
                          *(float*)( cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)) )/ 2;
        
        float boxdist_x  =( -(*(float*)( cur+sizeof(char)+sizeof(bool)+sizeof(float))) +
                           *(float*)( cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float))  )/ 2;
        
        float dist_x    = p.x_val - center_x;
        sum    += dist_x * dist_x;
        boxsum += boxdist_x * boxdist_x;
        
        // cur += sizeof(float)+sizeof(float);
        
        
        float center_y  =( (*(float*) (cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float))) +
                          *(float*)(cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)))/ 2;
        float boxdist_y  =( -(*(float*) (cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float))) +
                           *(float*)(cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)) )/ 2;
        
        float dist_y    = p.y_val - center_y;
        sum    += dist_y * dist_y;
        boxsum += boxdist_y * boxdist_y;
        
        //  cur += sizeof(float)+sizeof(float);
        bool canCorrelate = sqrt(sum) - sqrt(boxsum) < rad;
        
        if(!(canCorrelate)){
            return make_pair(0, false) ;
            
        }else{
            cur    += sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float);
            //call left
            char * pointerToRightchild=cur;
            cur+=sizeof(char * );
            
            pair<int,bool> res1=performPointCorr_IntOut(p, cur, rad);
            bool nextIsRight=res1.second;
            
            if(!nextIsRight){
                cur=(*(char * *)pointerToRightchild);
            }
            pair<int,bool> res2= performPointCorr_IntOut(p,cur , rad);
            return make_pair(res1.first+res2.first, res2.second);
        }
    }
}



void  copyNodes(char * & cur, char * & curOut){
    
    
    if(*cur == LEAF_TAG ){
        
        * curOut = LEAF_TAG;
        
        //cur++;
        //curOut++;
        *((float *)(curOut+sizeof(char)))= *((float *)(cur+sizeof(char)));
        
        *((float *)(curOut+sizeof(char)+sizeof(float)))=
        *((float *)(cur+sizeof(char)+sizeof(float)));
        
        //cur += sizeof(float);
        //curOut += sizeof(float);
        *((int *)(curOut+sizeof(char)+sizeof(float)+sizeof(float)))=
        (*(int *)(cur+sizeof(char)+sizeof(float)+sizeof(float)));
        
        // cur += sizeof(int);
        //curOut += sizeof(int);
        cur+= sizeof(char)+sizeof(float)+sizeof(float)+sizeof(int);
        curOut+=sizeof(char)+sizeof(float)+sizeof(float)+sizeof(int);
        return ;
        
    }else {
        *curOut = INNER_TAG ;
        //cur++;
        // curOut++;
        
        *((bool *)(curOut+sizeof(char)))=   *((bool *)(cur+sizeof(char)));
        // cur += sizeof(bool);
        // curOut += sizeof(bool);
        
        *((float *)(curOut+sizeof(char)+sizeof(bool)))=   *((float *)(cur+sizeof(char)+sizeof(bool)));
        //  cur += sizeof(float);
        //  curOut += sizeof(float);
        
        *((float *)(curOut+sizeof(char)+sizeof(bool)+sizeof(float)))=   *((float *)(cur+sizeof(char)+sizeof(bool)+sizeof(float)));
        //cur += sizeof(float);
        //curOut += sizeof(float);
        
        *((float *)(curOut+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)))=
        *((float *)(cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)));
        //   cur+=sizeof(float);
        //  curOut += sizeof(float);
        
        *((float *)(curOut+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)))=
        *((float *)(cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)));
        //cur += sizeof(float);
        // curOut += sizeof(float);
        
        
        *((float *)(curOut+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)))=
        *((float *)(cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)));
        //  cur+=sizeof(float);
        //  curOut += sizeof(float);
        cur+=+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float);
        curOut += sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float);
        copyNodes(cur,curOut);
        
        copyNodes(cur ,curOut);
        return;
    }
    
}




void performPointCorr_treeOut_rec(Point & p,char * & cur,char * & curOut,float rad){
    
    if(*cur == LEAF_TAG ){
        
        * curOut = LEAF_TAG;
        
        // cur++;
        // curOut++;
        float leaf_x = *((float *)(cur+sizeof(char))) ;
        *((float *)(curOut+sizeof(char)))=leaf_x;
        
        
        // cur += sizeof(float);
        //curOut+=sizeof(float);
        float  leaf_y = *((float *)(cur+sizeof(char)+sizeof(float)) );
        *((float *)(curOut+sizeof(char)+sizeof(float)))=leaf_y;
        
        //cur += sizeof(float);
        //curOut += sizeof(float);
        *((int *)(curOut+sizeof(char)+sizeof(float)+sizeof(float)))=
        (*(int *)(cur+sizeof(char)+sizeof(float)+sizeof(float)));
        
        float d = 0;
        d +=(p.x_val - leaf_x) * (p.x_val - leaf_x);
        d +=(p.y_val - leaf_y) * (p.y_val - leaf_y);
        
        if(sqrt(d) < rad){
            (*(int * )(curOut+sizeof(char)+sizeof(float)+sizeof(float)))++;
#ifdef TEST
            counter2++;
#endif
            
        }
        cur += sizeof(char)+sizeof(float)+sizeof(float)+sizeof(int);
        curOut += sizeof(char)+sizeof(float)+sizeof(float)+sizeof(int);
        
        return ;
        
    }else {
        *curOut = INNER_TAG ;
        //cur++;
        //curOut++;
        
        //well the performance be effected if at this point
        //cur is casted to pointer of Node_Inner and members where accessed using ->?? should try it!
        
        float sum    = 0.0;
        float boxsum = 0.0;
        *((bool *)(curOut+sizeof(char)))=   *((bool *)(cur+sizeof(char)));
        //        cur += sizeof(bool);
        //      curOut += sizeof(bool);
        
        *((float *)(curOut+sizeof(char)+sizeof(bool)))=   *((float *)(cur+sizeof(char)+sizeof(bool)));
        //cur += sizeof(float);
        //curOut += sizeof(float);
        
        
        float center_x  =( (*(float*) (cur+sizeof(char)+sizeof(bool)+sizeof(float))) +
                          *(float*)( cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)) )/ 2;
        
        float boxdist_x  =( -(*(float*)( cur+sizeof(char)+sizeof(bool)+sizeof(float))) +
                           *(float*)( cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float))  )/ 2;
        
        float dist_x    = p.x_val - center_x;
        sum    += dist_x * dist_x;
        boxsum += boxdist_x * boxdist_x;
        
        *((float *)(curOut+sizeof(char)+sizeof(bool)+sizeof(float)))=
        *((float *)(cur+sizeof(char)+sizeof(bool)+sizeof(float)));
        
        //cur += sizeof(float);
        //curOut += sizeof(float);
        
        
        *((float *)(curOut+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)))=
        *((float *)(cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)));
        //cur+=sizeof(float);
        //curOut += sizeof(float);
        
        
        float center_y  =( (*(float*) (cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float))) +
                          *(float*)(cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)))/ 2;
        float boxdist_y  =( -(*(float*) (cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float))) +
                           *(float*)(cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)) )/ 2;
        float dist_y    = p.y_val - center_y;
        sum    += dist_y * dist_y;
        boxsum += boxdist_y * boxdist_y;
        
        
        *((float *)(curOut+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)))=
        *((float *)(cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)));
        
        //cur += sizeof(float);
        //curOut += sizeof(float);
        
        
        *((float *)(curOut+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)))=
        *((float *)(cur+sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)));
        
        cur    += sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float);
        curOut += sizeof(char)+sizeof(bool)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float)+sizeof(float);
        //
        
        bool canCorrelate = sqrt(sum) - sqrt(boxsum) < rad;
        
        if(!(canCorrelate)){
            copyNodes(cur, curOut);
            copyNodes(cur, curOut);
            
        }else{
            //call left
            performPointCorr_treeOut_rec(p, cur,curOut,rad);
            
            performPointCorr_treeOut_rec(p,cur ,curOut, rad);
            return;
        }
    }
}
