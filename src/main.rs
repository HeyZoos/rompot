enum Register {
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    ProgramCounter,
    COND,
    COUNT,
}

enum MemoryMappedRegister {
    KeyboardStatus = 0xFE00,
    KeyboardData = 0xFE02,
}

#[derive(num_derive::FromPrimitive)]
enum Op {
    BR,
    ADD,
    LD,
    ST,
    JSR,
    AND,
    LDR,
    STR,
    RTI,
    NOT,
    LDI,
    STI,
    JMP,
    RES,
    LEA,
    TRAP,
}

enum Condition {
    POS = 1 << 0,
    ZRO = 1 << 1,
    NEG = 1 << 2,
}

type Memory = [u16; std::u16::MAX as usize];
type RegisterMemory = [u16; Register::COUNT as usize];

fn main() {
    let mut memory: Memory = [0; std::u16::MAX as usize];
    let mut registers: RegisterMemory = [0; Register::COUNT as usize];

    const PC_START: u16 = 0x3000;

    registers[Register::ProgramCounter as usize] = PC_START;

    println!("{:b}", -9i16);

    let window = pancurses::initscr();
    window.printw("Hello Rust");
    window.refresh();
    window.getch();
    pancurses::endwin();

    loop {
        let instruction: u16 = memory[registers[Register::ProgramCounter as usize] as usize];
        let operation = num::FromPrimitive::from_u16(instruction >> 12).unwrap();

        match operation {
            Op::ADD => op_add(instruction, &mut registers),
            Op::LD => op_ld(instruction, &mut registers, &mut memory),
            Op::LDI => op_ldi(instruction, &mut registers, &mut memory),
            Op::LEA => op_lea(instruction, &mut registers),
            _ => (),
        }
    }

    let args: Vec<String> = std::env::args().collect();

    println!("Hello, world!");
}

fn op_add(instruction: u16, registers: &mut RegisterMemory) {
    let dr = (instruction >> 9) & 0b0000_0000_0000_0111;
    let sr1 = (instruction >> 6) & 0b0000_0000_0000_0111;
    let imm_flag = (instruction >> 5) & 0b0000_0000_0000_0001;

    if imm_flag == 1 {
        let imm5: u16 = sign_extend(instruction & 0b0000_0000_0001_1111, 5);
        registers[dr as usize] = registers[sr1 as usize] + imm5;
    } else {
        let sr2 = instruction & 0b0000_0000_0000_0111;
        registers[dr as usize] = registers[sr1 as usize] + registers[sr2 as usize];
    }

    update_flags(dr, registers);
}

/// An address is computed by sign-extending bits [8:0] to 16 bits and adding
/// this value to the incremented PC. The contents of memory at this address
/// are loaded into DR. The condition codes are set, based on whether the value
/// loaded is negative, zero, or positive.
///
/// ## Example
///
/// LD R4, VALUE ; R4 ← mem[VALUE]
fn op_ld(instruction: u16, registers: &mut RegisterMemory, memory: &mut Memory) {
    let dr = (instruction >> 9) & 0b111;
    let pc_offset = instruction & 0b1_1111_1111;
    let pc = registers[Register::ProgramCounter as usize];
    let read_addr = pc + sign_extend(pc_offset, 9);

    registers[dr as usize] = memory[read_addr as usize];
    update_flags(dr, registers);
}

/// An address is computed by sign-extending bits [8:0] to 16 bits and adding
/// this value to the incremented PC. What is stored in memory at this address
/// is the address of the data to be loaded into DR. The condition codes are
/// set, based on whether the value loaded is negative, zero, or positive.
///
/// ## Example
///
/// LDI R4, ONEMORE ; R4 ← mem[mem[ONEMORE]]
fn op_ldi(instruction: u16, registers: &mut RegisterMemory, memory: &mut Memory) {
    let dr = (instruction >> 9) & 0b111;
    let pc_offset = instruction & 0b1_1111_1111;
    let pc = registers[Register::ProgramCounter as usize];
    let read_addr = pc + sign_extend(pc_offset, 9);

    registers[dr as usize] = mem_read(mem_read(read_addr, memory), memory);
    update_flags(dr, registers);
}

/// An address is computed by sign-extending bits [5:0] to 16 bits and adding
/// this value to the contents of the register specified by bits [8:6]. The
/// contents of memory at this address are loaded into DR. The condition codes
/// are set, based on whether the value loaded is negative, zero, or positive.
///
/// ## Example
///
/// LDR R4, R2, #−5 ; R4 ← mem[R2 − 5]
fn op_ldr(instruction: u16, registers: &mut RegisterMemory, memory: &mut Memory) {
    let dr = (instruction >> 9) & 0b111;
    let base_r = (instruction >> 6) & 0b111;
    let pc_offset = instruction & 0b11_1111;
    let read_addr = base_r + sign_extend(pc_offset, 6);

    registers[dr as usize] = mem_read(read_addr, memory);
    update_flags(dr, registers);
}

/// An address is computed by sign-extending bits [8:0] to 16 bits and adding
/// this value to the incremented PC. This address is loaded into DR. The
/// condition codes are set, based on whether the value loaded is negative,
/// zero, or positive.
///
/// LEA R4, TARGET ; R4 ← address of TARGET.
fn op_lea(instruction: u16, regs: &mut RegisterMemory) {
    let dr = (instruction >> 9) & 0b111;
    let pc_offset = instruction & 0b1_1111_1111;
    let pc = regs[Register::ProgramCounter as usize];

    regs[dr as usize] = pc + sign_extend(pc_offset, 9);
    update_flags(dr, regs);
}

/// Video explanation of the two's complement.
///
/// https://youtu.be/dHB7jFjESLY
fn sign_extend(n: u16, bit_count: usize) -> u16 {
    if (n >> (bit_count - 1)) & 1 == 1 {
        // n = 10111 (-9)
        // bit_count = 5
        //
        // n >> (5 - 1) = 00001
        // 00001 & 1 = 1
        // 0xFFFF = 1111_1111_1111_1111 << 5 = 1111_1111_1110_0000
        // 10111 | 1111_1111_1110_0000
        n | (0xFFFF << bit_count)
    } else {
        n
    }
}

fn update_flags(register_index: u16, registers: &mut RegisterMemory) {
    if registers[register_index as usize] == 0 {
        registers[Register::COND as usize] = Condition::ZRO as u16;
    } else if registers[register_index as usize] >> 15 == 1 {
        registers[Register::COND as usize] = Condition::NEG as u16;
    } else {
        registers[Register::COND as usize] = Condition::POS as u16;
    }
}

fn mem_write(address: u16, value: u16, memory: &mut Memory) {
    memory[address as usize] = value;
}

fn mem_read(address: u16, memory: &mut Memory) -> u16 {
    if address == MemoryMappedRegister::KeyboardStatus as u16 {
        // if ()
    }

    memory[address as usize]
}

#[cfg(test)]
mod tests {

    #[test]
    fn test_sign_extend() {}
}
