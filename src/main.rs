use macro_extra::ident_match;

fn align_up(addr: u64, size: u64) -> u64 {
    (addr + size - 1) & !(size - 1)
}

fn is_aligned(addr: u64, size: u64) -> bool {
    (addr & (size - 1)) == 0
}

fn main() {
    let base = 0x500_000_000;
    let addr = align_up(base+17*1024*1024*1024+1024*1024, 16);
    let compressed = (addr - base) >> 2;
    println!("{:b}", compressed);

    println!("addr: {:x}", addr);
    println!("compressed: {:x}", compressed);
    println!("{} {}", is_aligned(compressed, 16), is_aligned(addr, 16));
    println!("decompressed: {:x}", base + compressed * 8);
}