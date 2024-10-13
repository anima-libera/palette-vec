use palette_vec::{AutoMemoryOptimizationPolicyNever, OutPalVec, PalVec};

use clap::Parser;

#[derive(Parser)]
#[command(color = clap::ColorChoice::Auto)]
struct CommandLineSettings {
    #[arg(long)]
    many_instance_count: usize,

    #[arg(long)]
    few_instance_count: usize,

    #[arg(long)]
    how_many_manies: usize,

    #[arg(long)]
    how_many_fews: usize,

    #[arg(long)]
    mid_size_min: usize,
    #[arg(long)]
    mid_size_max: usize,
    #[arg(long)]
    mid_size_step: usize,

    #[arg(long)]
    how_many_mids: usize,
}

fn main() {
    let settings = CommandLineSettings::parse();

    let manies = std::iter::repeat(settings.many_instance_count).take(settings.how_many_manies);
    let fews = std::iter::repeat(settings.few_instance_count).take(settings.how_many_fews);
    let mids = std::iter::repeat(settings.mid_size_min).take(settings.how_many_mids);
    let composition: Vec<usize> = manies.chain(fews).chain(mids).collect();
    let mid_values = (settings.how_many_manies + settings.how_many_fews)
        ..(settings.how_many_manies + settings.how_many_fews + settings.how_many_mids);

    let mut simple_pal_vec = PalVec::new();
    let mut out_pal_vec: OutPalVec<_, AutoMemoryOptimizationPolicyNever> = OutPalVec::new();

    for (element, instance_count) in composition.iter().copied().enumerate() {
        simple_pal_vec.push(element, instance_count);
        out_pal_vec.push(element, instance_count);
    }

    let mut mid_size = settings.mid_size_min;
    while mid_size <= settings.mid_size_max {
        out_pal_vec.perform_memory_opimization();

        println!(
            "{}, {}",
            simple_pal_vec.used_memory(),
            out_pal_vec.used_memory()
        );

        mid_size += settings.mid_size_step;
        for mid_value in mid_values.clone() {
            simple_pal_vec.push(mid_value, settings.mid_size_step);
            out_pal_vec.push(mid_value, settings.mid_size_step);
        }
    }
}
