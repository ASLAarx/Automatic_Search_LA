# -*- coding: utf-8 -*-


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
    

def speck(Len,Round,k):
    #SAT model of linear approximations for SPECK
    
    solv=Solver()
    
    Input_mask_Left=[i for i in range(1,(int(Len/2))+1)]
    
    
    
    Input_mask_Right=[i+int(Len/2) for i in range(1,(int(Len/2))+1)]
    solv.add_clause(Input_mask_Left+Input_mask_Right)
    temp=Len
    if (Len==32):
        alpha=7
        beta=2
    else:
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
        
    
        
    a=[]
    for i in range(Round):
        a=a+z[i]
    Input_mask=[i+1 for i in range(Len)]
    solv.add_clause(Input_mask)
    
    b=[[(k*i)+j+1+temp for j in range(k)] for i in range((Round*int(Len/2))-1)]
    seq_add(a,b,(Round*int(Len/2)),k,solv)  
    temp+=k*((Round*int(Len/2))-1)
    
    
    
    a=solv.solve()  
    print (a[0]) 
    


Len=128 #block size
Round=7 #number of rounds
print ("number of rounds:  "+str(Round))
k=12 #correlation is higher than 2^-k
print ("correlation: 2^-"+str(k))



speck(Len,Round,k)

time2=time.process_time()
print ("time:  ",time2-time1)














