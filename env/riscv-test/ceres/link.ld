OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS
{
  . = 0x80000000;
  
  .text.init : { *(.text.init) }
  
  /* tohost için sadece 8-byte hizalama yeterli */
  . = ALIGN(8);
  .tohost : { *(.tohost) }
  
  /* Normal kod için 4-byte hizalama */
  . = ALIGN(4);
  .text : { *(.text) }
  
  /* Data için 8-byte hizalama (double-word için) */
  . = ALIGN(8);
  .data : { *(.data) }
  
  .bss : { *(.bss) }
  
  /* Signature sections (test framework için) */
  . = ALIGN(4);
  .signature : { 
    *(.signature)
    *(begin_signature)
    *(end_signature)
  }
  
  _end = .;
}