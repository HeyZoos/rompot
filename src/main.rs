use byteorder::{BigEndian, ReadBytesExt};
use num_derive::FromPrimitive;
use std::io::Read;

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

#[derive(Debug, FromPrimitive)]
enum Op {
    ADD = 0b0001,
    AND = 0b0101,
    BR = 0b0000,
    JMP = 0b1100,
    JSR = 0b0100,
    LD = 0b0010,
    LDI = 0b1010,
    LDR = 0b0110,
    LEA = 0b1110,
    NOT = 0b1001,
    RES = 0b1101,
    RTI = 0b1000,
    ST = 0b0011,
    STI = 0b1011,
    STR = 0b0111,
    TRAP = 0b1111,
}

#[derive(Debug, FromPrimitive)]
enum Trap {
    /// Get character from keyboard, not echoed onto the terminal.
    GETC = 0x20,

    /// Output a character.
    OUT = 0x21,

    /// Output a word string.
    PUTS = 0x22,

    /// Get character from keyboard, echoed onto the terminal.
    IN = 0x23,

    /// Output a byte string.
    PUTSP = 0x24,

    /// Halt the program.
    HALT = 0x25,
}

enum Condition {
    POS = 1 << 0,
    ZRO = 1 << 1,
    NEG = 1 << 2,
}

type Memory = [u16; std::u16::MAX as usize];
type Registers = [u16; Register::COUNT as usize];

///
///
///
#[derive(argh::FromArgs)]
struct Args {
    /// input file
    #[argh(option)]
    file: Option<String>,
}

struct Machine {
    is_running: bool,
}

fn main() {
    let args: Args = argh::from_env();

    if args.file.is_none() {
        println!("You need to supply an `.lc3` --file!");
        return;
    }

    let mut memory = [0; std::u16::MAX as usize];
    let mut registers = [0; Register::COUNT as usize];
    let mut state = Machine { is_running: true };

    const PC_START: u16 = 0x3000;

    registers[Register::ProgramCounter as usize] = PC_START;

    read_image_file(args.file.unwrap(), &mut memory);

    let window = pancurses::initscr();

    while state.is_running {
        std::thread::sleep(std::time::Duration::from_millis(1000));

        window.clear();
        window.printw(format!("Sleep Time (ms): {}\n", 1000));

        let pc = registers[Register::ProgramCounter as usize];
        let instruction: u16 = memory[pc as usize];
        let opcode = instruction >> 12;
        let operation = num::FromPrimitive::from_u16(opcode).unwrap();

        window.printw(format!("About to execute: {:b}", &opcode));

        match operation {
            Op::ADD => op_add(instruction, &mut registers),
            Op::AND => op_and(instruction, &mut registers),
            Op::BR => op_br(instruction, &mut registers),
            Op::JMP => op_jmp(instruction, &mut registers),
            Op::JSR => op_jsr(instruction, &mut registers),
            Op::LD => op_ld(instruction, &mut registers, &mut memory),
            Op::LDI => op_ldi(instruction, &mut registers, &mut memory),
            Op::LDR => op_ldr(instruction, &mut registers, &mut memory),
            Op::LEA => op_lea(instruction, &mut registers),
            Op::NOT => op_not(instruction, &mut registers),
            Op::RES => panic!("Reserved cannot be used."),
            Op::RTI => op_rti(instruction, &mut registers),
            Op::ST => op_st(instruction, &mut registers),
            Op::STI => op_sti(instruction, &mut registers, &mut memory),
            Op::STR => op_str(instruction, &mut registers, &mut memory),
            Op::TRAP => op_trap(instruction, &mut registers, &mut memory, &mut state),
        }

        registers[Register::ProgramCounter as usize] += 1;

        window.refresh();
    }

    pancurses::endwin();
}

fn op_add(instruction: u16, registers: &mut Registers) {
    let dr = (instruction >> 9) & 0b111;
    let sr1 = (instruction >> 6) & 0b111;
    let imm_flag = (instruction >> 5) & 0b1;

    if imm_flag == 1 {
        let imm5: u16 = sign_extend(instruction & 0b1_1111, 5);
        registers[dr as usize] = registers[sr1 as usize] + imm5;
    } else {
        let sr2 = instruction & 0b111;
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
fn op_ld(instruction: u16, regs: &mut Registers, mem: &mut Memory) {
    let dr = (instruction >> 9) & 0b111;
    let pc_offset = instruction & 0b1_1111_1111;
    let pc = regs[Register::ProgramCounter as usize];
    let read_addr = pc + sign_extend(pc_offset, 9);

    regs[dr as usize] = mem[read_addr as usize];
    update_flags(dr, regs);
}

/// An address is computed by sign-extending bits [8:0] to 16 bits and adding
/// this value to the incremented PC. What is stored in memory at this address
/// is the address of the data to be loaded into DR. The condition codes are
/// set, based on whether the value loaded is negative, zero, or positive.
///
/// ## Example
///
/// LDI R4, ONEMORE ; R4 ← mem[mem[ONEMORE]]
fn op_ldi(instruction: u16, regs: &mut Registers, mem: &mut Memory) {
    let dr = (instruction >> 9) & 0b111;
    let pc_offset = instruction & 0b1_1111_1111;
    let pc = regs[Register::ProgramCounter as usize];
    let read_addr = pc + sign_extend(pc_offset, 9);

    regs[dr as usize] = mem_read(mem_read(read_addr, mem), mem);
    update_flags(dr, regs);
}

/// An address is computed by sign-extending bits [5:0] to 16 bits and adding
/// this value to the contents of the register specified by bits [8:6]. The
/// contents of memory at this address are loaded into DR. The condition codes
/// are set, based on whether the value loaded is negative, zero, or positive.
///
/// ## Example
///
/// LDR R4, R2, #−5 ; R4 ← mem[R2 − 5]
fn op_ldr(instruction: u16, registers: &mut Registers, mem: &mut Memory) {
    let dr = (instruction >> 9) & 0b111;
    let base_r = (instruction >> 6) & 0b111;
    let pc_offset = instruction & 0b11_1111;
    let read_addr = base_r + sign_extend(pc_offset, 6);

    registers[dr as usize] = mem_read(read_addr, mem);
    update_flags(dr, registers);
}

/// An address is computed by sign-extending bits [8:0] to 16 bits and adding
/// this value to the incremented PC. This address is loaded into DR. The
/// condition codes are set, based on whether the value loaded is negative,
/// zero, or positive.
///
/// ## Example
///
///     LEA R4, TARGET ; R4 ← address of TARGET.
fn op_lea(instruction: u16, regs: &mut Registers) {
    let dr = (instruction >> 9) & 0b111;
    let pc_offset = instruction & 0b1_1111_1111;
    let pc = regs[Register::ProgramCounter as usize];

    regs[dr as usize] = pc + sign_extend(pc_offset, 9);
    update_flags(dr, regs);
}

/// The bit-wise complement of the contents of SR is stored in DR. The
/// condition codes are set, based on whether the binary value produced, taken
/// as a 2’s complement integer, is negative, zero, or positive.
fn op_not(instruction: u16, regs: &mut Registers) {
    let dr = (instruction >> 9) & 0b111;
    let sr = (instruction >> 6) & 0b111;
    regs[dr as usize] = sr.wrapping_neg(); // <3
    update_flags(dr, regs);
}

/// The program unconditionally jumps to the location specified by the contents
/// of the base register. Bits [8:6] identify the base register.
///
/// The RET instruction is a special case of the JMP instruction. The PC is
/// loaded with the contents of R7, which contains the linkage back to the
/// instruction following the subroutine call instruction.
///
/// ## Example
///
///     JMP R2 ; PC ← R2
///     RET ; PC ← R7
fn op_jmp(instruction: u16, regs: &mut Registers) {
    let base_r = (instruction >> 6) & 0b111;
    regs[Register::ProgramCounter as usize] = regs[base_r as usize];
}

/// The condition codes specified by the state of bits [11:9] are tested. If
/// bit [11] is set, N is tested; if bit [11] is clear, N is not tested. If bit
/// [10] is set, Z is tested, etc. If any of the condition codes tested is set,
/// the program branches to the location specified by adding the sign-extended
/// PCoffset9 field to the incremented PC.
///
/// ## Example
///
///     BRzp LOOP ; Branch to LOOP if the last result was zero or positive.
///     BR NEXT ; Unconditionally branch to NEXT.
fn op_br(instruction: u16, regs: &mut Registers) {
    let pc_offset = instruction & 0b1_1111_1111;
    let n = (instruction >> 9 & 1) == 1;
    let z = (instruction >> 10 & 1) == 1;
    let p = (instruction >> 11 & 1) == 1;
    let pc = regs[Register::ProgramCounter as usize];
    let cond = regs[Register::COND as usize];

    if (n && cond == Condition::NEG as u16)
        || (z && cond == Condition::ZRO as u16)
        || (p && cond == Condition::POS as u16)
    {
        regs[pc as usize] = pc + sign_extend(pc_offset, 9)
    }
}

/// First, the incremented PC is saved in R7. This is the linkage back to the
/// calling routine. Then the PC is loaded with the address of the first
/// instruction of the subroutine, causing an unconditional jump to that
/// address. The address of the subroutine is obtained from the base register
/// (if bit [11] is 0), or the address is computed by sign-extending bits
/// [10:0] and adding this value to the incremented PC (if bit [11] is 1).
///
/// ## Example
///
///     JSR QUEUE ; Put the address of the instruction following JSR into R7;
///               ; Jump to QUEUE.
///     JSRR R3 ; Put the address following JSRR into R7; Jump to the
///             ; address contained in R3.
fn op_jsr(instruction: u16, regs: &mut Registers) {
    let bit11 = (instruction >> 11) & 0b1;

    if bit11 == 0 {
        let base_r = (instruction >> 6) & 0b111;
        regs[Register::ProgramCounter as usize] = regs[base_r as usize];
    } else {
        let pc_offset = instruction & 0b111_1111_1111;
        regs[Register::ProgramCounter as usize] =
            regs[Register::ProgramCounter as usize] + sign_extend(pc_offset, 11);
    }

    regs[Register::R7 as usize] = regs[Register::ProgramCounter as usize];
}

/// The contents of the register specified by SR are stored in the memory
/// location whose address is computed by sign-extending bits [8:0] to 16 bits
/// and adding this value to the incremented PC.
///
/// ## Example
///
/// ST R4, HERE ; mem[HERE] ← R4
fn op_st(instruction: u16, regs: &mut Registers) {
    let sr = (instruction >> 9) & 0b111;
    let pc_offset = instruction & 0b1_1111_1111;
    let pc = regs[Register::ProgramCounter as usize];
    regs[(pc + sign_extend(pc_offset, 9)) as usize] = regs[sr as usize];
}

/// The contents of the register specified by SR are stored in the memory
/// location whose address is obtained as follows: Bits [8:0] are sign-extended
/// to 16 bits and added to the incremented PC. What is in memory at this
/// address is the address of the location to which the data in SR is stored.
///
/// ## Example
///
///     STI R4, NOT_HERE ; mem[mem[NOT_HERE]] ← R4
fn op_sti(instruction: u16, regs: &mut Registers, mem: &mut Memory) {
    let sr = (instruction >> 9) & 0b111;
    let pc_offset = instruction & 0b1_1111_1111;
    let pc = regs[Register::ProgramCounter as usize];
    let write_addr = pc + sign_extend(pc_offset, 9);

    mem[mem[write_addr as usize] as usize] = regs[sr as usize];
}

/// The contents of the register specified by SR are stored in the memory
/// location whose address is computed by sign-extending bits [5:0] to 16
/// bits and adding this value to the contents of the register specified
/// by bits [8:6].
///
/// ## Example
///
///     STR R4, R2, #5 ; mem[R2 + 5] ← R4
fn op_str(instruction: u16, regs: &mut Registers, mem: &mut Memory) {
    let sr = (instruction >> 9) & 0b111;
    let base_r = (instruction >> 6) & 0b111;
    let pc_offset = instruction & 0b11_1111;
    let write_addr = regs[base_r as usize] + sign_extend(pc_offset, 6);

    mem[write_addr as usize] = regs[sr as usize];
}

/// If bit [5] is 0, the second source operand is obtained from SR2. If bit
/// [5] is 1, the second source operand is obtained by sign-extending the imm5
/// field to 16 bits. In either case, the second source operand and the
/// contents of SR1 are bitwise ANDed, and the result stored in DR. The
/// condition codes are set, based on whether the binary value produced, taken
/// as a 2’s complement integer, is negative, zero, or positive.
///
/// ## Example
///
/// ```
/// AND R2, R3, R4 ;R2 ← R3 AND R4
/// AND R2, R3, #7 ;R2 ← R3 AND 7
/// ```
fn op_and(instruction: u16, regs: &mut Registers) {
    let dr = (instruction >> 9) & 0b111;
    let bit5 = instruction >> 5 & 0b1;
    let sr1 = (instruction >> 6) & 0b111;

    if bit5 == 0 {
        let sr2 = instruction & 0b111;
        regs[dr as usize] = regs[sr1 as usize] & regs[sr2 as usize];
    } else {
        let imm5 = instruction & 0b1_1111;
        regs[dr as usize] = regs[sr1 as usize] & sign_extend(imm5, 5);
    }

    update_flags(dr, regs);
}

///
///
///

///
///
///
fn op_rti(instruction: u16, regs: &mut Registers) {
    todo!()
}

///
///
///
fn op_trap(instruction: u16, regs: &mut Registers, mem: &mut Memory, state: &mut Machine) {
    let trapvect8 = instruction & 0b1111_1111;
    let trapcode = num::FromPrimitive::from_u16(trapvect8).unwrap();

    match trapcode {
        Trap::GETC => trap_getc(regs),
        Trap::HALT => trap_halt(state),
        Trap::IN => trap_in(regs),
        Trap::OUT => trap_out(regs),
        Trap::PUTS => trap_puts(regs, mem),
        Trap::PUTSP => trap_putsp(regs, mem),
    }
}

fn trap_getc(regs: &mut Registers) {
    let input: Option<u16> = std::io::stdin()
        .bytes()
        .next()
        .and_then(|result| result.ok())
        .map(|byte| byte as u16);

    regs[Register::R0 as usize] = input.unwrap();
}

fn trap_halt(state: &mut Machine) {
    state.is_running = false;
}

fn trap_in(regs: &mut Registers) {
    print!("Enter a character: ");

    let input = std::io::stdin()
        .bytes()
        .next()
        .and_then(|result| result.ok())
        .map(|byte| byte as u16)
        .unwrap();

    print!("{}", input as u8 as char);

    regs[Register::R0 as usize] = input;
}

fn trap_out(regs: &mut Registers) {
    print!("{}", regs[Register::R0 as usize] as u8 as char);
}

fn trap_puts(regs: &mut Registers, mem: &mut Memory) {
    let mut pointer = regs[Register::R0 as usize];

    loop {
        let word = vec![mem[pointer as usize]];

        if word[0] == 0 {
            break;
        }

        let ch: Vec<char> = std::char::decode_utf16(word).map(|r| r.unwrap()).collect();
        print!("{}", ch[0]);
        pointer += 1;
    }
}

fn trap_putsp(regs: &mut Registers, mem: &mut Memory) {
    let mut pointer = regs[Register::R0 as usize];

    loop {
        let word = mem[pointer as usize];

        if word == 0 {
            break;
        }

        let char1 = (word & 0xFF) as u8;
        print!("{}", char1 as char);
        let char2 = (word >> 8) as u8;
        if char2 != 0 {
            print!("{}", char2 as char);
        }

        pointer += 1;
    }
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

fn update_flags(register_index: u16, registers: &mut Registers) {
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

fn read_image_file(path: String, memory: &mut Memory) {
    let mut file = std::fs::File::open(path).unwrap();
    let mut origin = file.read_u16::<BigEndian>().unwrap();
    while let Ok(word) = file.read_u16::<BigEndian>() {
        memory[origin as usize] = word;
        origin += 1;
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn test_sign_extend() {}
}
