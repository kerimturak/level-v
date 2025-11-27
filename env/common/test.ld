OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY {
  RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 32K
}

SECTIONS {
  /* Start at base of RAM */
  . = ORIGIN(RAM);

  .text.init : {
    *(.text.init)
  } > RAM

  . = ALIGN(64);
  .tohost : {
    *(.tohost)
  } > RAM

  .text : {
    *(.text)
  } > RAM

  .data : {
    *(.data)
  } > RAM

  .sdata : {
    __global_pointer$ = . + 0x800;
    *(.srodata*)
    *(.sdata*)
  } > RAM

  .sbss : {
    *(.sbss*)
    *(.scommon)
  } > RAM

  .bss : {
    *(.bss*)
  } > RAM

  /* Thread local */
  .tdata : {
    _tdata_begin = .;
    *(.tdata)
    _tdata_end = .;
  } > RAM

  .tbss : {
    *(.tbss)
    _tbss_end = .;
  } > RAM

  _end = .;

  /* Stack RAM sonunda */
  _stack_top = ORIGIN(RAM) + LENGTH(RAM);
}
