mod types;

use crate::types::StatefulList;

use argh::FromArgs;

use byteorder::{BigEndian, ReadBytesExt};

use num::FromPrimitive;
use num_derive::FromPrimitive;

use std::io;
use std::io::Read;
use std::thread;
use std::time::{Duration, Instant};

use tui::backend::CrosstermBackend;
use tui::layout::{Constraint, Direction, Layout};
use tui::style::{Modifier, Style, Color};
use tui::text::{Span, Spans};
use tui::widgets::{Block, Borders, List, ListItem, ListState, Table, Row};
use tui::Terminal;

/**
 * TODO(jesse)
 *
 * [ ] - Investigate how to get rid of the copious amount of `as` casts.
 * [ ] - Get test coverage to 100.
 */

enum _Event<I> {
    Input(I),
    Tick,
}

enum Register {
    R0,
    _R1,
    _R2,
    _R3,
    _R4,
    _R5,
    _R6,
    R7,
    PC,
    COND,
    COUNT,
}

enum MemoryMappedRegister {
    KeyboardStatus = 0xFE00,
    _KeyboardData = 0xFE02,
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

/// Crossterm demo
#[derive(Debug, FromArgs)]
struct Cli {
    /// butts
    #[argh(option)]
    file: Option<String>,

    /// time in ms between two ticks.
    #[argh(option, default = "250")]
    tick_rate: u64,
    /// whether unicode symbols are used to improve the overall look of the app
    #[argh(option, default = "true")]
    enhanced_graphics: bool,
}

struct Vm {
    instr: u16,
    mem: Memory,
    on: bool,
    regs: Registers,
    instruction_history: StatefulList<String>,
}

impl Vm {
    fn new() -> Self {
        let mut regs = [0; Register::COUNT as usize];
        regs[Register::PC as usize] = 0x3000;

        Self {
            instr: 0,
            mem: [0; std::u16::MAX as usize],
            on: true,
            regs,
            instruction_history: StatefulList::new(),
        }
    }

    /// Loads a program located at `path` into memory.
    fn load(&mut self, path: String) {
        let mut file = std::fs::File::open(path).unwrap();
        let mut origin = file.read_u16::<BigEndian>().unwrap();
        while let Ok(word) = file.read_u16::<BigEndian>() {
            self.mem[origin as usize] = word;
            origin += 1;
        }
    }

    fn pc(&self) -> u16 {
        self.regs[Register::PC as usize]
    }

    fn opcode(&self) -> u16 {
        self.instr >> 12
    }

    fn op(&self) -> Op {
        FromPrimitive::from_u16(self.opcode()).unwrap()
    }

    fn step(&mut self) {
        self.instr = self.mem[self.pc() as usize];

        match self.op() {
            Op::ADD => op_add(self.instr, &mut self.regs),
            Op::AND => op_and(self.instr, &mut self.regs),
            Op::BR => op_br(self.instr, &mut self.regs),
            Op::JMP => op_jmp(self.instr, &mut self.regs),
            Op::JSR => op_jsr(self.instr, &mut self.regs),
            Op::LD => op_ld(self.instr, &mut self.regs, &mut self.mem),
            Op::LDI => op_ldi(self.instr, &mut self.regs, &mut self.mem),
            Op::LDR => op_ldr(self.instr, &mut self.regs, &mut self.mem),
            Op::LEA => op_lea(self.instr, &mut self.regs),
            Op::NOT => op_not(self.instr, &mut self.regs),
            Op::RES => panic!("Reserved cannot be used."),
            Op::RTI => op_rti(),
            Op::ST => op_st(self.instr, &mut self.regs),
            Op::STI => op_sti(self.instr, &mut self.regs, &mut self.mem),
            Op::STR => op_str(self.instr, &mut self.regs, &mut self.mem),
            Op::TRAP => {
                let trapvect8 = self.instr & 0b1111_1111;
                let trapcode = num::FromPrimitive::from_u16(trapvect8).unwrap();

                match trapcode {
                    Trap::GETC => trap_getc(&mut self.regs),
                    Trap::HALT => trap_halt(self),
                    Trap::IN => trap_in(&mut self.regs),
                    Trap::OUT => trap_out(&mut self.regs),
                    Trap::PUTS => trap_puts(&mut self.regs, &mut self.mem),
                    Trap::PUTSP => trap_putsp(&mut self.regs, &mut self.mem),
                }
            }
        }

        self.instruction_history
            .items
            .push_front(format!("{}", self.instr));
        self.regs[Register::PC as usize] += 1;
    }
}

fn main() -> Result<(), io::Error> {
    let args: Cli = argh::from_env();

    if args.file.is_none() {
        println!("You need to supply an `.obj` --file!");
        return Ok(());
    }

    let mut vm = Vm::new();

    vm.load(args.file.unwrap());

    let stdout = io::stdout();
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    // let mut app = App::new("Crossterm Demo", cli.enhanced_graphics);

    // let (tx, rx) = modifiex::channel();

    let tick_rate = Duration::from_millis(1000);
    thread::spawn(move || {
        let last_tick = Instant::now();
        loop {
            // poll for tick rate duration, if no events, sent tick event.
            let _timeout = tick_rate
                .checked_sub(last_tick.elapsed())
                .unwrap_or_else(|| Duration::from_secs(0));

            // if event::poll(timeout).unwrap() {
            // if let CEvent::Key(key) = event::read().unwrap() {
            //     tx.send(Event::Input(key)).unwrap();
            // }
            // }

            // if last_tick.elapsed() >= tick_rate {
            //     tx.send(Event::Tick).unwrap();
            //     last_tick = Instant::now();
            // }
        }
    });

    let mut state: Vec<String> = vec![];
    let mut list_state = ListState::default();

    while vm.on {
        terminal.clear().unwrap();

        let mut instruction = format!("{}", vm.instr);
        let _instruction_clone = instruction.clone();

        terminal
            .draw(|frame| {
                let sections = Layout::default()
                    .direction(Direction::Horizontal)
                    .margin(1)
                    .constraints(
                        [
                            Constraint::Percentage(25),
                            Constraint::Percentage(50),
                            Constraint::Percentage(25),
                        ]
                        .as_ref(),
                    )
                    .split(frame.size());

                let tasks: Vec<ListItem> = vm
                    .instruction_history
                    .items
                    .iter()
                    .map(|i| ListItem::new(vec![Spans::from(Span::raw(i))]))
                    .collect();

                let instruction_list_widget = List::new(tasks)
                    .block(Block::default().borders(Borders::ALL).title("Instructions"))
                    .highlight_style(Style::default().add_modifier(Modifier::BOLD))
                    .highlight_symbol("> ");

                frame.render_stateful_widget(instruction_list_widget, sections[0], &mut list_state);

                let block = Block::default().title("Memory").borders(Borders::ALL);
                frame.render_widget(block, sections[1]);

                let rows = vm.regs.iter().enumerate().map(|(idx, reg)| {
                    let hex_val = format!("0x{:0>4x}", reg);
                    let idx_s = format!("Register {}", idx);
                    Row::Data(vec![idx_s, hex_val].into_iter())
                });

                let register_table_widget = Table::new(["Name", "Value"].iter(), rows)
                    .block(Block::default().borders(Borders::ALL).title("Registers"))
                    .highlight_symbol(">> ")
                    .widths(&[Constraint::Percentage(50), Constraint::Percentage(50)]);

                frame.render_widget(register_table_widget, sections[2]);
            })
            .unwrap();

        std::thread::sleep(std::time::Duration::from_millis(1000));

        vm.step();
        instruction = format!("{}", vm.instr);
        state.push(instruction);
    }

    Ok(())
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
    let pc = regs[Register::PC as usize];
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
    let pc = regs[Register::PC as usize];
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
    let pc = regs[Register::PC as usize];

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
    regs[Register::PC as usize] = regs[base_r as usize];
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
    let pc = regs[Register::PC as usize];
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
        regs[Register::PC as usize] = regs[base_r as usize];
    } else {
        let pc_offset = instruction & 0b111_1111_1111;
        regs[Register::PC as usize] = regs[Register::PC as usize] + sign_extend(pc_offset, 11);
    }

    regs[Register::R7 as usize] = regs[Register::PC as usize];
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
    let pc = regs[Register::PC as usize];
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
    let pc = regs[Register::PC as usize];
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
fn op_rti() {
    todo!()
}

fn trap_getc(regs: &mut Registers) {
    let input: Option<u16> = std::io::stdin()
        .bytes()
        .next()
        .and_then(|result| result.ok())
        .map(|byte| byte as u16);

    regs[Register::R0 as usize] = input.unwrap();
}

fn trap_halt(vm: &mut Vm) {
    vm.on = false;
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
