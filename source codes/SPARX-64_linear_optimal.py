# -*- coding: utf-8 -*-
#sparx64

from pycryptosat import Solver
import random
import time

import subprocess
time1=time.process_time()


    
def branching_linear(a,b,c,solv):
    # SAT model of linear approximations for branching operation
    solv.add_clause([a,b,-c])
    solv.add_clause([a,-b,c])
    solv.add_clause([-a,b,c])
    solv.add_clause([-a,-b,-c])
    
def xor_linear(a,b,c,solv):
    # SAT model of linear approximations for XOR operation
    solv.add_clause([a,-b])
    solv.add_clause([-a,b])
    solv.add_clause([a,-c])
    solv.add_clause([-a,c])
    


def mod_linear(a,b,c,z,n,solv):
    #SAT model of linear approximations for modular addition
    solv.add_clause([-z[n-1]])
    for j in range(1,n):
        solv.add_xor_clause([a[n-j],b[n-j],c[n-j],z[n-j],z[n-j-1]],False)
        solv.add_clause([z[n-j],-a[n-j],c[n-j]])
        solv.add_clause([z[n-j],a[n-j],-c[n-j]])
        solv.add_clause([z[n-j],b[n-j],-c[n-j]])
        solv.add_clause([z[n-j],-b[n-j],c[n-j]])
        
    solv.add_clause([z[0],-a[0],c[0]])
    solv.add_clause([z[0],a[0],-c[0]])
    solv.add_clause([z[0],b[0],-c[0]])
    solv.add_clause([z[0],-b[0],c[0]])
        
    # solv.add_xor_clause([var_temp[0],a[0],b[0],c[0]],False)
    # solv.add_clause([-z[0],var_temp[0]])

        
def seq_add(a,b,n,k,solv):      
    # SAT model to describe a[0]+a[1]+...+a[n-1]<=k, where b is an auxiliary variable
    if k==0:
        for i in range(n):
            solv.add_clause([-a[i]])
    else:
        solv.add_clause([-a[0],b[0][0]])
        for j in range(1,k):
            solv.add_clause([-b[0][j]])
        for i in range(1,n-1):
            # print (i)
            solv.add_clause([-a[i],b[i][0]])
            solv.add_clause([-b[i-1][0],b[i][0]])
            for j in range(1,k):
                solv.add_clause([-a[i],-b[i-1][j-1],b[i][j]])
                solv.add_clause([-b[i-1][j],b[i][j]])
            solv.add_clause([-a[i],-b[i-1][k-1]])
        solv.add_clause([-a[n-1],-b[n-2][k-1]])
    
def A(solv,Input_mask_Left,Input_mask_Right,z,temp): #SAT model of linear approximations for round function
    alpha=7
    beta=2
    Len=32
    
    Input_mask_Left=[Input_mask_Left[(j+alpha)%(16)] for j in range(16)]
    
    c=[temp+j+1 for j in range(int(Len/2))]
    temp +=int(Len/2)

    
    
    mask_temp=[temp+j+1 for j in range(int(Len/2))]
    temp +=int(Len/2)    
    
    
    mod_linear(Input_mask_Left,mask_temp,c,z,(int(Len/2)),solv)
    
        
    Input_mask_Left=c
    
    Input_mask_Right_new=[temp+j+1 for j in range(int(Len/2))]
    temp +=int(Len/2)
    
    for j in range(int(Len/2)):
        branching_linear(Input_mask_Right[j],mask_temp[j],Input_mask_Right_new[j],solv)
    Input_mask_Right=Input_mask_Right_new 
    
    Input_mask_Right=[Input_mask_Right[(i+(int(Len/2))-beta)%(int(Len/2))] for i in range(int(Len/2))]
    
    Input_mask_Left_new=[temp+j+1 for j in range(int(Len/2))]
    temp +=int(Len/2)
    
    for j in range(int(Len/2)):
        branching_linear(Input_mask_Right[j],Input_mask_Left[j],Input_mask_Left_new[j],solv)
    Input_mask_Left=Input_mask_Left_new
    
    return (Input_mask_Left,Input_mask_Right,temp)

def A3(solv,Input_mask_Left,Input_mask_Right,z,temp): #SAT model of linear approximations for three round functions in a step structure
    mask_temp=[]
    for i in range(3):
        (Input_mask_Left,Input_mask_Right,temp)=A(solv,Input_mask_Left,Input_mask_Right,z[i],temp)
        mask_temp=mask_temp+[[Input_mask_Left]+[Input_mask_Right]]
    return (Input_mask_Left,Input_mask_Right,mask_temp,temp)

def L2(solv,Input_mask0,Input_mask1,temp): #SAT model of linear approximations for linear layer in a step structure
    center_mask=[temp+i+1 for i in range(len(Input_mask0))]
    temp+=len(Input_mask0)
    
    Input_mask0_new=[temp+i+1 for i in range(len(Input_mask0))]
    temp+=len(Input_mask0)
    
    Input_mask1_new=[temp+i+1 for i in range(len(Input_mask0))]
    temp+=len(Input_mask0)
    
    
    
    for i in range(len(Input_mask0)):
        solv.add_xor_clause([Input_mask0[i],Input_mask0_new[i],center_mask[i]],False)
        solv.add_xor_clause([Input_mask1[i],Input_mask1_new[i],center_mask[i]],False)
        
    
    center_mask=[center_mask[(i+8)%16] for i in range(16)]
    
    for i in range(len(Input_mask0)):
        solv.add_xor_clause([Input_mask0_new[i],Input_mask1_new[i],center_mask[i]],False)
        # solv.add_clause([-Input_mask0_new[i],center_mask[i]])
        # solv.add_clause([-Input_mask1_new[i],center_mask[i]])
        # solv.add_clause([-Input_mask2_new[i],center_mask[i]])
        # solv.add_clause([-Input_mask3_new[i],center_mask[i]])
        
        # solv.add_clause([Input_mask0_new[i],-center_mask[i]])
        # solv.add_clause([Input_mask1_new[i],-center_mask[i]])
        # solv.add_clause([Input_mask2_new[i],-center_mask[i]])
        # solv.add_clause([Input_mask3_new[i],-center_mask[i]])
        
    return (Input_mask0_new,Input_mask1_new,temp)


def step64(solv,Input_mask0,Input_mask1,Input_mask2,Input_mask3,all_mask,z_temp,temp):
    #SAT model of linear approximations for a step structure
    z0=[z_temp[i][0] for i in range(3)]
    z1=[z_temp[i][1] for i in range(3)]
   
    
    (Input_mask0,Input_mask1,mask_temp0,temp)=A3(solv,Input_mask0,Input_mask1,z0,temp)
    (Input_mask2,Input_mask3,mask_temp1,temp)=A3(solv,Input_mask2,Input_mask3,z1,temp)
   
    
    
    #print ('mask_temp0',mask_temp0) 
    all_mask=all_mask+[mask_temp0[j]+mask_temp1[j]  for j in range(3)]
    #print (all_mask)
    
    Input_mask0_new=[temp+i+1 for i in range(len(Input_mask0))]
    temp+=len(Input_mask0)
    Input_mask1_new=[temp+i+1 for i in range(len(Input_mask0))]
    temp+=len(Input_mask0)
    
    
    Input_mask0_right=[temp+i+1 for i in range(len(Input_mask0))]
    temp+=len(Input_mask0)
    Input_mask1_right=[temp+i+1 for i in range(len(Input_mask0))]
    temp+=len(Input_mask0)
   
    
    for i in range(len(Input_mask0)):
        solv.add_xor_clause([Input_mask0[i],Input_mask0_new[i],Input_mask0_right[i]],False)
        solv.add_xor_clause([Input_mask1[i],Input_mask1_new[i],Input_mask1_right[i]],False)
       
        
        
    (Input_mask0_out,Input_mask1_out,temp)=L2(solv,Input_mask0_right,Input_mask1_right,temp)
    
    for i in range(len(Input_mask0)):
        solv.add_clause([-Input_mask0_out[i],Input_mask2[i]])
        solv.add_clause([-Input_mask1_out[i],Input_mask3[i]])
        
        
        solv.add_clause([Input_mask0_out[i],-Input_mask2[i]])
        solv.add_clause([Input_mask1_out[i],-Input_mask3[i]])
        
    all_mask=all_mask+ [[Input_mask2]+[Input_mask3]+[Input_mask0_new]+[Input_mask1_new]]   
    return (Input_mask2,Input_mask3,Input_mask0_new,Input_mask1_new,all_mask,temp)

    
    
    
    
    
    


def linear_distin():
    
    solv=Solver() #construct SAT instance "slover"
    Len=64 #block size
    Round=13  #number of round function
    k=30  #correlation is higher than 2^-k
        
    step_num=Round//3 #number of step structure
    rou_add=Round%3   #remaining rounds after step_num step structure
        
    # initial 128-bit input linear masks
    Input_mask0=[i+1 for i in range(16)]
    Input_mask1=[i+1+16 for i in range(16)] 
    Input_mask2=[i+1+32 for i in range(16)]
    Input_mask3=[i+1+48 for i in range(16)]
        
    temp=64
        
    #corrlation related to modular operation, z[i][j] describe the correlation of modular addition in j-th word of i-th round
    z=[[[temp+int(i*Len/2)+(k*int(Len/2/2))+1+j for j in range(int(Len/2/2))] for k in range(2)] for i in range(Round)]
        
    #number of variables has been used
    temp+=Round*int(Len/2)
        
        
    all_mask=[]  #all linear mask in each round function are stored in list "all_mask"
    for i in range(step_num):
        z_temp=[z[j] for j in range(3*i,(3*i)+3)]
        # establish SAT model of linear approximation for i-th step struture
        (Input_mask0,Input_mask1,Input_mask2,Input_mask3,all_mask,temp)=step64(solv,Input_mask0,Input_mask1,Input_mask2,Input_mask3,all_mask,z_temp,temp)
        
        
        
            
    for i in range(rou_add):
        # establish SAT model of linear approximation for remaining round function
        (Input_mask0,Input_mask1,temp)=A(solv,Input_mask0,Input_mask1,z[(3*step_num)+i][0],temp)
        (Input_mask2,Input_mask3,temp)=A(solv,Input_mask2,Input_mask3,z[(3*step_num)+i][1],temp)
            
        # store linear masks of current round function in list "all_mask"
        all_mask=all_mask+[[Input_mask0]+[Input_mask1]+[Input_mask2]+[Input_mask3]]
        
    all_mask=[[[j+1+(k*16) for j in range(16)] for k in range(4)]]+all_mask
    #print (all_mask[6])
    all_mask=[[[all_mask[i][j][16-k-1] for k in range(16)] for j in range(4)] for i in range(Round+1+step_num)]
        
        
        
    solv.add_clause([i+1 for i in range(64)])
        
        
    a=[]
    for i in range(Round):
        for j in range(2):
            a=a+z[i][j]
        
    b=[[(k*i)+j+1+temp for j in range(k)] for i in range((Round*int(Len/2))-1)]
    # establish SAT model to describe \sum_{i,j,l}z[i][j][l]<=k, i.e. add constraints such that the correlation is at least 2^-k 
    seq_add(a,b,(Round*int(Len/2)),k,solv)  
        
    temp+=k*((Round*int(Len/2))-1)
        
        
        
        
        
    print ("block size： "+str(Len))
    print ("number of rounds:  "+str(Round))
    print ("correlation: 2^-"+str(k))
        
    # solve SAT instance "solv", the solution is stored in "solution"
    solution=solv.solve()
    print (solution[0])
        
        
        
        
        
        
        

        


          
linear_distin()   
    





   

time2=time.process_time()
print (time2-time1)













