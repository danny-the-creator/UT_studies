.data
message: .asciiz "Memory allocated: "   # Define the message string    
prompt: .asciiz "Enter a number (12-bit): "  # Message to prompt user
offset: .byte 4
seq_: .byte 5		# sequence of numbers
len_: .byte 12
.text
.globl main

main:
    # Directly initialize values for n and b
    
    lb  $t1, seq_          # Load immediate value 5 into $t1 (n)
    lb  $t2, len_          # Load immediate value 8 into $t2 (b)
	move $a0, $t1              # Move the value into $a0 (for printing)
    	li $v0, 1                 # Syscall to print integer
    	syscall
    	move $a0, $t2              # Move the value into $a0 (for printing)
    	li $v0, 1                 # Syscall to print integer
    	syscall