# -*- coding: utf-8 -*-

# the intermediate linear mask is fixed as 0x0000 0000 0000 0001 0000 0000 0000 0000
from pycryptosat import Solver
import time
import os
import subprocess
import time
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
    



def mod_linear(a,b,c,z,var_temp,n,solv):
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
    

def speck_firstpart(solv,Round,k):
    #SAT model of linear approximations for first part of SPECK
    Len=128
    Input_mask_Left=[i for i in range(1,(int(Len/2))+1)]
    
    
    
    Input_mask_Right=[i+int(Len/2) for i in range(1,(int(Len/2))+1)]
    temp=Len
    
    alpha=8
    beta=3
    
    z=[[temp+(i*int(Len/2))+1+j for j in range(int(Len/2))]for i in range(Round)]
    temp+=Round*int(Len/2)
    
    for i in range(Round):
        Input_mask_Left=[Input_mask_Left[(j+alpha)%(int(Len/2))] for j in range(int(Len/2))]
        
        c=[temp+j+1 for j in range(int(Len/2))]
        temp +=int(Len/2)
    
        var_temp=[temp+j+1 for j in range(int(Len/2))]
        temp +=int(Len/2)
        
        mask_temp=[temp+j+1 for j in range(int(Len/2))]
        temp +=int(Len/2)
        
        mod_linear(Input_mask_Left,mask_temp,c,z[i],var_temp,(int(Len/2)),solv)
        
            
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
    
    #linear mask after first part is fixed as 0x0000 0000 0000 0001 0000 0000 0000 0000
    solv.add_clause([Input_mask_Left[0]])
    for i in range(1,int(Len/2)):
        solv.add_clause([-Input_mask_Left[i]])
    for i in range(int(Len/2)):
        solv.add_clause([-Input_mask_Right[i]])
        
    a=[]
    for i in range(Round):
        a=a+z[i]
    Input_mask=[i+1 for i in range(Len)]
    solv.add_clause(Input_mask)
    
    b=[[(k*i)+j+1+temp for j in range(k)] for i in range((Round*int(Len/2))-1)]
    seq_add(a,b,(Round*int(Len/2)),k,solv)  

    temp+=k*((Round*int(Len/2))-1)
    
    
def speck_secondpart(solv,Round,k):
    #SAT model of linear approximations for second part of SPECK
    Len=128
    
    alpha=8
    beta=3
    
    
    Input_mask_Left=[i for i in range(1,(int(Len/2))+1)]
    
    #linear mask before second part is fixed as 0x0000 0000 0000 0001 0000 0000 0000 0000
    for i in range(2,Len+1):
        solv.add_clause([-i])
    solv.add_clause([1])
    
    

    
    
    Input_mask_Right=[i+int(Len/2) for i in range(1,(int(Len/2))+1)]
    temp=Len
    
    
    z=[[temp+(i*int(Len/2))+1+j for j in range(int(Len/2))]for i in range(Round)]
    temp+=Round*int(Len/2)
    all_mask=[0 for i in range(Round+1)]
    all_mask[0]=[Input_mask_Left[int(Len/2)-1-i] for i in range(int(Len/2))]+[Input_mask_Right[int(Len/2)-1-i] for i in range(int(Len/2))]
    for i in range(Round):
        Input_mask_Left=[Input_mask_Left[(j+alpha)%(int(Len/2))] for j in range(int(Len/2))]
        
        c=[temp+j+1 for j in range(int(Len/2))]
        temp +=int(Len/2)
    
        var_temp=[temp+j+1 for j in range(int(Len/2))]
        temp +=int(Len/2)
        
        mask_temp=[temp+j+1 for j in range(int(Len/2))]
        temp +=int(Len/2)
        
        mod_linear(Input_mask_Left,mask_temp,c,z[i],var_temp,(int(Len/2)),solv)
        
            
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
        
        all_mask[i+1]=[Input_mask_Left[int(Len/2)-1-j] for j in range(int(Len/2))]+[Input_mask_Right[int(Len/2)-1-j] for j in range(int(Len/2))]
        

    a=[]
    for i in range(Round):
         a=a+z[i]
    Input_mask=[i+1 for i in range(Len)]
    solv.add_clause(Input_mask)
    

    b=[[(k*i)+j+1+temp for j in range(k)] for i in range((Round*int(Len/2))-1)]
    seq_add(a,b,(Round*int(Len/2)),k,solv)  
    
    temp+=k*((Round*int(Len/2))-1)
    
    

def speck_twopart(Round1,k1,Round2,k2):
    #search for linear approximation of first part with correlation 2^-k1 and second part with correlation 2^-k2
    solv0=Solver() 
    speck_firstpart(solv0,Round1,k1)
    a=solv0.solve()  
    print ("first part: ",a[0]) 
    
                
    
    solv1=Solver()
    speck_secondpart(solv1,Round2,k2)
    b=solv1.solve() 
    print ("second part: ",b[0]) 
    



Round1=5 #number of rounds for the first part
print ("first part, number of rounds:  "+str(Round1))
k1=12 #correlation of the first part is higher than 2^-k1
print ("correlation: 2^-"+str(k1))
Round2=12 #number of rounds for the second part
print ("second part, number of rounds:  "+str(Round2))
k2=48 #correlation of the second part is higher than 2^-k2
print ("correlation: 2^-"+str(k2))


speck_twopart(Round1,k1,Round2,k2)

time2=time.process_time()
print (time2-time1)













