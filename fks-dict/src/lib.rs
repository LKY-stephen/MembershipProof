
use std::{collections::HashSet};
use num_primes::{Verification, BigUint};

// FKS dictionary
// The structure store the FKS dictionary and modular p and a
// the first layer hash h1(x)=x*store[0] mod p mod a;
// if h1(x) is not 0:
//   the second layer hash h2(x) = x*store[h1[x]+1] mod p mod store[h1[x]]
// The implementation is not fully optmized for space usage.
/*
 WARNING
 1. We use u32 to store elements, in worst case each u32 element needs
 6 times space for achieving o(1) access. 
 Users should use this implementation no more than around 2^29( around 536 million) u32 elements.
 2. The modular p is also an u32 elements, hence the max value is around
 4,294,967,290 (4,294,967,291 is the biggest prime of u32)
 3. zero is used for not exist element, hence do not insert into the dictionary.
*/

pub struct FKSDict {
    p: u32,
    a: u32,
    store: Vec<u32>,
}


impl FKSDict {

    pub fn new(input: &HashSet<u32>, max: u32) -> FKSDict {
        let n :u32 = input.len()as u32;
        // smallest prime bigger than max
        let mut p =  if (max & 1) == 0 { max+1 } else  { max }; 
        while Verification::is_composite(&BigUint::from(p)) {
            p+=2;
        } 
        
        // Init first layer hash
        let mut group: Vec<HashSet<u32>>;
        let mut k=1;

        loop {
            group = compute_collision(input, k, p, n);
            let mut sum = 0;
            for x in group.iter() {
                let l = x.len();
                sum += l*l;
            }
            if sum > (3*n) as usize { k+=1; continue; }
            break;
        }
        
        // Fill dictionary
        let mut dict: Vec<u32> = Vec::new();
        dict.push(k);
        let mut w:Vec<u32>=Vec::new();

        let mut pointer = n+1;
        for x in group.iter() {
            let s:u32 = (x.len()) as u32;
            if s > 0 {
                let w_size:u32 = s*s;
                w.push(w_size);
                let mut k2 =1;
                // Fill the second layer
                loop {
                    let subgroup=compute_collision(x, k2, p, w_size);

                    if (&subgroup).into_iter().any(|z| z.len()>1) {k2+=1; continue;}
                    
                    w.push(k2);
                    for e in subgroup.iter() {
                        if e.is_empty() {
                            w.push(0);
                        }
                        else {
                            w.push(*e.iter().next().unwrap() as u32);
                        }
                    }
                    break;
                }

                dict.push(pointer);
                pointer += w_size+2;
            }
            else {
                dict.push(0)
            }
        }
        assert_eq!(dict.len(), 1+n as usize);
        assert_eq!(dict.len()+w.len(), pointer as usize);
        dict.append(&mut w);
        return FKSDict{
            p: p,
            a: n,
            store: dict,
        };
    }

    // Query if an element is stored in the dictionary
    pub fn query(&self, x: u32) -> bool {
        !self.gen_proof(x).ends_with(&[0]) 
    }

    // Generate a constant size proof for (non)-membership
    pub fn gen_proof(&self, x:u32) -> Vec<u32>{
        let h1 = perfect_hash(x, self.store[0], self.p, self.a)+1;
        let w = self.store[h1 as usize]; 
        if w == 0 {return vec![self.store[0], self.p, self.a,0]};
        let k2:u32 =  self.store[1+w as usize];
        let r:u32 = self.store[w as usize];
        
        let y =  perfect_hash(
            x,
            k2,
            self.p,
            r);
        if self.store[(2+w+y )as usize] != x {return vec![self.store[0], self.p, self.a, w, k2, r,0];}
        return vec![self.store[0], self.p, self.a, w, k2, r,x];
    }

    // verify if an membership apply to the dictionary
    // return true if it is an valid proof(both member or non-member)
    pub fn verify(&self, x: u32, proof: &[u32]) -> bool {

        if proof[0] != self.store[0] ||
        proof[1]!= self.p ||
        proof[2]!= self.a ||
        proof[3]!= self.store[1+perfect_hash(x,  proof[0] ,  proof[1] ,  proof[2] ) as usize] {
            return false;
        }

        if proof[3] == 0 && proof.len()==4{
            return true;
        }

        if proof[4]!=self.store[1+proof[3] as usize] ||
        proof[5] != self.store[proof[3] as usize] ||
        proof[6] != self.store[(2+proof[3]+perfect_hash(x, proof[4], self.p, proof[5]) )as usize]{
            return false;
        }

        return true;
    }

}

fn compute_collision(input: &HashSet<u32>, k: u32, p:u32, a:u32)->Vec<HashSet<u32>>{
    let mut v = vec![HashSet::new(); a as usize];
    for x in input.iter() {
        v[perfect_hash(*x, k, p, a) as usize].insert(*x);
    }
    return v;
}

fn perfect_hash(x:u32, k: u32, p: u32, a: u32) -> u32 {
    let y= ((x as u64 * k as u64) % p as u64) as u32;
    return y %a;
}