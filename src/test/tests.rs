use rand::{thread_rng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

use crate::test::*;

#[test]
fn random_test() {
    let tests = [(5, 10, 5, 3, 0.5, 100)];
    for (var_num, node_num, inst_num, use_num, density, times) in tests.iter() {
        for _ in 0..*times {
            let mut seed: <ChaCha8Rng as SeedableRng>::Seed = Default::default();
            thread_rng().fill(&mut seed);
            println!(
                "random_test_seeded({:?}, {}, {}, {}, {}, {});",
                seed, var_num, node_num, inst_num, use_num, density
            );
            random_test_seeded(seed, *var_num, *node_num, *inst_num, *use_num, *density);
        }
    }
}
