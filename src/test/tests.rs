use rand::{thread_rng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

use crate::test::*;

#[test]
fn random_test() {
    random_test_seeded([133, 13, 110, 176, 175, 84, 19, 154, 29, 201, 2, 21, 135, 171, 226, 31, 114, 175, 93, 113, 127, 126, 161, 157, 113, 155, 177, 179, 243, 231, 68, 96], 5, 10, 5, 3, 0.5);
    let tests = [(5, 10, 5, 3, 0.5, 1)];
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
