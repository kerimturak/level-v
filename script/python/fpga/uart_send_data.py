"""
Bilgisayar üzerinden fpga de yüklü olan işlemciye uart ile veri bu dosyadan yazılır (rom a program yazma)
"""
import serial

port = 'COM3'
baud_rate = 115200

test = "./tests/hex_test/test.hex" #im

# RV32I
coremark_rv32i_1      = "./tests/hex_test/50MHz/RV32I/coremark/iteration_1_test/coremark_baremetal_static.hex"
coremark_rv32i_1000   = "./tests/hex_test/50MHz/RV32I/coremark/iteration_1000/coremark_baremetal_static.hex"
dhrystone_I_2000000     = "./tests/hex_test/50MHz/RV32I/dhrystone/iteration_2000000/dhrystone_static.hex"

# RV32IC
coremark_rv32ic_1     = "./tests/hex_test/50MHz/RV32IC/coremark/iteration_1_test/coremark_baremetal_static.hex"
coremark_rv32ic_1000  = "./tests/hex_test/50MHz/RV32IC/coremark/iteration_1000/coremark_baremetal_static.hex"
dhrystone_IC_2000000     = "./tests/hex_test/50MHz/RV32IC/dhrystone/iteration_2000000/dhrystone_static.hex"


# RV32IC
coremark_rv32imc_1    = "./tests/hex_test/50MHz/RV32IMC/coremark/iteration_1_test/coremark_baremetal_static.hex"
coremark_rv32imc_1000 = "./tests/hex_test/50MHz/RV32IMC/coremark/iteration_1000/coremark_baremetal_static.hex"
coremark_rv32imc_1100 = "./tests/hex_test/50MHz/RV32IMC/coremark/iteration_1100/coremark_baremetal_static.hex"
dhrystone_IMC_8000000     = "./tests/hex_test/50MHz/RV32IMC/dhrystone/iteration_8000000/dhrystone_static.hex"

file = coremark_rv32imc_1100

program_sequence = "ceresTEST"

file_format = 1

if file_format == 1:
    program_data = open(file, 'r').read()
    lines = program_data.split('\n')

    ser = serial.Serial(port, baud_rate)
    ser.timeout = 1

    ser.write(program_sequence.encode('utf-8'))
    print(program_sequence)

    hex_str = hex(len(lines))
    print ("Number of Instruction is " + str(len(lines)) + " = " + hex_str)

    hex_str = int(hex_str, 16).to_bytes(4, 'big')
    ser.write(hex_str)

    for line in lines:
        if len(line) < 8:
            read_data = read_data
        else:
            read_data = int(line, 16).to_bytes(4, 'big')
            ser.write(read_data)

        print("{:02x}".format(read_data[0]) + \
        "{:02x}".format(read_data[1]) + \
        "{:02x}".format(read_data[2]) + \
        "{:02x}".format(read_data[3]) )
    ser.write('done'.encode('utf-8'))

elif file_format == 2:
    program_data = open(file, 'rb').read()
    ser = serial.Serial(port, baud_rate)
    ser.timeout = 1

    ser.write(program_sequence.encode('utf-8'))
    print(program_sequence)

    hex_str = hex(len(program_data))
    print ("Number of Instruction is " + str(len(program_data)) + " = " + hex_str)

    hex_str = int(hex_str, 16).to_bytes(4, 'big')
    ser.write(hex_str)

    for i in range(0, len(program_data), 4):
        ser.write(program_data[i+3])
        ser.write(program_data[i+2])
        ser.write(program_data[i+1])
        ser.write(program_data[i])

        #print("{:02x}".format(program_data[i+3]) + \
        #"{:02x}".format(program_data[i+2]) + \
        #"{:02x}".format(program_data[i+1]) + \
        #"{:02x}".format(program_data[i]) )
    ser.write('done'.encode('utf-8'))

print("Done Programming")
print(hex_str)

