OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY
{
  RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 64K
}

SECTIONS
{
  .text.init :
  {
    KEEP(*(.text.init))
  } > RAM

  .text :
  {
    *(.text*)
  } > RAM

  .rodata :
  {
    *(.rodata*)
  } > RAM

  .data :
  {
    *(.data*)
    *(.sdata*)
    __global_pointer__ = .;
  } > RAM

  .bss (NOLOAD) :
  {
    __bss_start = .;
    *(.bss*)
    *(.sbss*)
    *(COMMON)
    __bss_end = .;
  } > RAM

  _stack_top = ORIGIN(RAM) + LENGTH(RAM);
}
