
struct FKSDict<'a> {
    mod1: u32,
    mod2: u32,
    length:u32,
    _array: &'a [u32],
}

impl FKSDict<'_> {

    fn new(n: &[u32], m: u32) -> FKSDict {
    
        unimplemented!();
    }

    fn query(x: u32) -> bool {

        unimplemented!();
    }


    fn proof(x:u32) -> &'static [u32] {

        unimplemented!();
    }

    fn verify(proof: &[u32]) -> bool {

        unimplemented!();
    }

}
