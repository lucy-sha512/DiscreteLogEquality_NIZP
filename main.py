
import random
import hashlib
import json

## Class: EllipticCurveArithmetic => defines the elliptic curve operations
# point addition, scalar multiplication, inverse modulo #
# Takes ecc parameters as object #

class EllipticCurveArithmetic:
    def __init__(self,ecc):
       self.ecc=ecc

    '''
    eeuclid_inverse_mod(self,q,p)=> Computes inverse modulo using Extended Euclidean algorithm
    Returns the inverse modulo z : (q*z) mod p == 1

    '''
    def eeuclid_inverse_mod(self, q, p):
        # Exception when dividend is zero
        if q == 0:
            raise ZeroDivisionError('Exception:Zero Division')
        # When the dividend is negative
        if q < 0:
            return p-self.eeuclid_inverse_mod(-q,p)
        
        # Extended Euclid Algorithm
        #Initialize the start variables x1, x2 and y1, y2
        x1, x2=0,1
        y1,y2=1,0
        #Initilaize z1, z2 as the p and q
        z1, z2=p,q

        #Find the quotient until remainder 0 is obtained
        while(z1 !=0):
            d=z2//z1 #quotient when p divides q
            z2,z1=z1, z2-d*z1 #new remainder is the dividend
            x2,x1=x1, x2-d*x1
            y2,y1=y1, y2-d*y1

        #Gcd is the non zero term after dividing q until z1 is 0
        # a=bq+r : Euclid's division rule
        #gcd=z
        z,x,y=z2,x2,y2

        assert z==1
        assert (q*x)% p == 1

        return x % p

    '''
    ecc_on_curve(self, point): Takes a point (x,y) and checks whether it is in
    secp256k1 curve or not. 
    Returns => True if point is in the curve
    Returns => False if point is not in the curve
    '''

    def ecc_on_curve(self,point):
        if point is None:
            return True

        x,y=point
        return (y * y - x * x * x - self.ecc["a"] * x - self.ecc["b"]) % self.ecc["p"] == 0
    
    '''
    ecc_add_points(self, point1 , point 2): Takes two points on the ECC curve of the form
    (point1_x, point1_y) and (point2_x, point2_y) and adds them to get another rpoint on the curve
    Returns  another point on the curve of the form (x,y)
    '''

    def ecc_add_points(self, point1 , point2):
        # Ensure  point 1 and point 2 are on the ECC curve
        assert self.ecc_on_curve(point1)
        assert self.ecc_on_curve(point2) 

        # If one of the point is infinity/none then it returns  the point with identity operation on point2/point1
        # 0+point2=point2
        if point1 is None:
            return point2
        if point2 is None:
            return point1

        x1,y1=point1
        x2,y2=point2

        # If both points are inverse of each other the result is 0
        if x1 == x2 and y1 != y2:
            return None

        # Slopes m when if both points are equal
        if x1 == x2:
            m = (3 * x1 * x1 + self.ecc["a"]) * self.eeuclid_inverse_mod(2 * y1, self.ecc["p"])
        else:
        #Slopes m when if both points are  unqual equal

            m = (y1 - y2) * self.eeuclid_inverse_mod(x1 - x2, self.ecc["p"])
        
        # Finding the resultant pointusing slopes and point 1 point2
        x3 = m * m - x1 - x2
        y3 = y1 + m * (x3 - x1)

        #The point is a reflection on along x -axis of the result
        result = (x3 % self.ecc["p"], -y3 % self.ecc["p"])

        # Ensure the result is on curve
        assert self.ecc_on_curve(result)

        return result

    '''
    ecc_scalar_multiplication(self,k, point): Multiples the point  tith a scalar k. In ECC scalar multiplication
    is achieved by adding the same point k times
    Returns the scaled point result
    '''

    def ecc_scalar_multiplication(self,k, point):
        
        #ensures the point is on the curve
        assert self.ecc_on_curve(point)

        #if k is multiple of order of the curve  or point is infinity
        if k % self.ecc["n"] == 0 or point is None:
            return None

        # if k is negative
        if k < 0:
            return self.ecc_scalar_multiplication(-k, self.ecc_point_negation(point))

        result = None
        addend = point

        # Add k times the point to itself  point+point+....... k times 
        while k:
            if k & 1:
                result = self.ecc_add_points(result, addend)

             # Double.
            addend = self.ecc_add_points(addend, addend)

            k >>= 1

        #Ensure the result is on the curve
        assert self.ecc_on_curve(result)

        return result

    '''
    ecc_point_negation: Negates a given point
    '''



    def ecc_point_negation(self,point):
        #Ensure the point is on the curve
        assert self.ecc_on_curve(point)
        # if point is infinity
        if point is None:
        
            return None

        x, y = point
        #Negate the y coordinate
        result = (x, -y % self.ecc["p"])
        #Ensure the result is on the curve
        assert self.is_on_curve(result)

        return result



## Class: DiscreteLogEquality_NIZK => Class inherits the EllipticCurveArithmetic Class objects
# Has two methods Prover and Verifier.
# Implements the prove and verification that Y=xG and Z=xM are from the same secret x



class DiscreteLogEquality_NIZK(EllipticCurveArithmetic):
    
    '''
    init method inherits the objects and methods of super class
    ecc{} dictionary containning secp256k1 curve paramters
    x is the object of this class 
    '''
    
    def __init__(self, ecc,x):
        super().__init__(ecc)
        self.x=x
        

    '''
    Prover(self,x): Implements the prover functionality where the Prover challenges the verifier by
    that value x is the secret without providing any information about x
    It generates random number k and calculates two pointsi A and B on ecc curve and commits to it
    It sends the committments with a challenge s to the verifier

    Returns a dictionary Proof with Provers commitment and challenge
    
    '''

    def Prover(self,x):
        print("\nStep 1: Prover generates random integers k and r\n")
        k=random.randint(0,self.ecc["n"]-1)
        r=random.randint(0,self.ecc["n"]-1)
       
        print(k)
        print(r)


        G=self.ecc["g"]
        print("Prover Calculates two points on ECC G and M")
        M=self.ecc_scalar_multiplication(r,G)
        print(G)
        print("\n")
        print(M)


        print("\n Prover calculates public key from G and M\n")
        print("\nY=xG\n")
        Y=self.ecc_scalar_multiplication(x,G)
        print(Y)

        print("\n Z=xM")
        Z=self.ecc_scalar_multiplication(x,M)
        print(Z)

        print("********* Prover has to prove xG = xM without revealing x ")

        print("\n Step 2: Prover computes A and B with k ")
        print("\n A=kG\n")
        A=self.ecc_scalar_multiplication(k,G)
        print(A)
        print("\n B=kM\n")
        B=self.ecc_scalar_multiplication(k,M)
        print(B)

        G_x,_ = G
        M_x,_ = M
        A_x,_ = A
        B_x,y = B
        Y_x,y = Y
        Z_x,_ = Y

        print("\n Prover Commits on A and B\n")


        c=hashlib.sha256(G_x.to_bytes(32,'big')+Y_x.to_bytes(32,'big')+M_x.to_bytes(32,'big')+Z_x.to_bytes(32,'big')+A_x.to_bytes(32,'big')+B_x.to_bytes(32,'big'))
        digest=c.hexdigest()
        c=int(digest,16)

        print("\n Step 3: Committment\n", c)

        print("\n Step 4: Prover Generates challenge: (k-c*x) mod n \n")

        s=(k-c*x)%self.ecc["n"]

        print(s)

        print("\n Packing the proof......\n")

        Proof={
            'committment':c,
            'challenge':s,
            'G':self.ecc["g"],
            'M':M,
            'Y':Y,
            'Z':Z
            
        }

        prover_data=json.dumps(Proof)
        print('\nProof sent\n')

        return prover_data

    '''
    Verifier(self, proof): Verifies the Proof sent by the Prover.
    Computes A' and B' by using the challenge s as follows:
    A'=sG+cY
    B'=sM+cZ
    if the proof is correct the A'=A and B'=B
    It commits on A' and B'
    '''
    def Verifier(self, proof):
        print("\n Step 5: Load Prover committment and challenge\n")
        prover_data=json.loads(proof)
        c=prover_data['committment']
        s=prover_data['challenge']
        print("\nLoaded\n")
        

        G=prover_data['G']
        M=prover_data['M']
        Y=prover_data['Y']
        Z=prover_data['Z']

        print("\nCommittment and Challenge Received\n")

    
        print("\n Step 6: Recompute Committment A' and B' from the challenge received\n") 
        A_=self.ecc_add_points(self.ecc_scalar_multiplication(s,G),self.ecc_scalar_multiplication(c,Y))
        B_= self.ecc_add_points(self.ecc_scalar_multiplication(s,M), self.ecc_scalar_multiplication(c,Z))


        
        G_x,_ = G
        M_x,_ = M
        A_x,_ = A_
        B_x,y = B_
        Y_x,y = Y
        Z_x,_ = Y

        c_=hashlib.sha256(G_x.to_bytes(32,'big')+Y_x.to_bytes(32,'big')+M_x.to_bytes(32,'big')+Z_x.to_bytes(32,'big')+A_x.to_bytes(32,'big')+B_x.to_bytes(32,'big'))
        digest=c_.hexdigest()
        c_=int(digest,16)

        print("\nPack the computed proof \n")

        Computed_Proof={
            'committment':c_,
            
            
        }

        verifier_data=json.dumps(Computed_Proof)
        return verifier_data

if __name__=='__main__':
    ecc={}
    ecc["name"]="secp256k1"
    ecc["p"]=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
    ecc["a"]=0
    ecc["b"]=7
    ecc["g"]=(0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
       0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8)
    ecc["n"]=0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
    ecc["h"]=1

    print("\nLoading ECC Paramters..........")
    print("\nCurve Type\t", ecc["name"])
    print("\nPrime Modulus \t", ecc["p"])
    print("\n Curve Coefficient a\t", ecc["a"])
    print("\n Curve Coefficient b\t", ecc["b"])
    print("\n Curve Equation a\t", "y^2=x^3+7")
    print("\n Generator Point \t", ecc["g"])
    print("\n Order of the Curvec ",ecc["n"])
    print("\n Subgroup  a\t", ecc["h"])

   

    x = random.randint(0, ecc["n"]-1)
    print("******** Non Interactive Discrete Log Equality***********")
    dle_nizk=DiscreteLogEquality_NIZK(ecc,x)
    
    print("\nProver\n:")
    prover=dle_nizk.Prover(x)
    prover_data=json.loads(prover)
    print("\nProvers's Commitment\n")
    print(prover_data)

    print("\n\n")

    print("Starting Verification....")

    verifier=dle_nizk.Verifier(prover)
    verifier_data=json.loads(verifier)

    print("\nVerifier's Commitment\n")
    print(verifier_data)

    print("\n Step 7: Check the committments c and c_ \n")

    c=prover_data["committment"]
    c_=verifier_data["committment"]

    if (c==c_):
        print("\nProove Successful\n")
    else:
        print("\nProove Unsuccesful\n")




