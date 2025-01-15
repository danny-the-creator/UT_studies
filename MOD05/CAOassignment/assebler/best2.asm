.data
prompt: .asciiz "Input number in bits: " # Store the prompt string
input_buffer: .space 256        # Buffer for input (adjust size as needed)
seq_: .word 3    # sequence of numbers
len_: .word 34
.text
.globl main

main:                    
    lw  $t1, seq_($zero)   
    lw  $t2, len_($zero)                

    
    move $t3, $t2            # Copy original value of b to $t3 for later use
    li $t3, 15                # Load immediate value 15 into $t0
    div $t2, $t3              # Divide $t2 by 15
    mflo $t2                  # Move the quotient into $t2
    mfhi $t4                  # Move the remainder into $t4

    bnez $t4, round_up       # If remainder is not zero, branch to round_up



# Continue here if no rounding is needed
j allocate_memory

round_up:		# t2 - len in half words
    addi $t2, $t2, 1               # Increment $t2 to round up




allocate_memory:
    move $t5, $zero                # Initialize $t5 to 0 (total number of halfwords to allocate)
    move $t3, $t1                  # Move seq_ to $t3 for the loop counter

add_halfwords:
    add $t5, $t5, $t2              # $t5 += $t2 (number of halfwords per element)
    addi $t3, $t3, -1              # Decrement the counter ($t3) by 1
    bne $t3, $zero, add_halfwords  # If $t3 (counter) != 0, go to add_halfwords

    # Since each halfword is 2 bytes, multiply the number of halfwords by 2 for total bytes
    sll $t5, $t5, 1                # $t5 = $t5 * 2
    
    move $t6, $t5		# is needed for combination



    # Syscall to allocate memory dynamically using sbrk
    li $v0, 9                      # Syscall number for sbrk
    move $a0, $t5                  # Pass total bytes to allocate
    syscall                        # Allocate memory
    move $s0, $v0                  # Save base address of the allocated memory in $s0


    # Input loop to get seq_ numbers from the user and store them in the array
    move $s2, $s0         # $s2 will be the pointer to the current array element
    move $t7, $zero       # Initialize the loop counter ($t7 = 0)

input_loop:  #get another value from a user

    move $t9, $t2                # Copy $t2 to $t9 for loop control
   
    # Print the prompt
    li $v0, 4                    # Syscall for print string
    la $a0, prompt               # Load address of prompt
    syscall                      # Print the prompt

    # Read the binary string input
    li $v0, 8                    # Syscall for reading a string
    la $a0, input_buffer         # Load address for input buffer
    li $a1, 60                  # Maximum number of characters to read
    syscall                      # Read string


    # Now, let's calculate the actual length (excluding newline)
    la $t0, input_buffer         # Load address of input buffer
    li $t5, 0                     # Initialize a counter for actual length

count_length1:
    lb $t8, 0($t0)               # Load the next byte from the input buffer
    beqz $t8, done_count1          # If null terminator, we are done
    beq $t8, 10, done_count1       # If newline character, we are also done
    addi $t5, $t5, 1             # Increment actual length counter
    addi $t0, $t0, 1             # Move to the next byte
    j count_length1                # Repeat until done

done_count1:
    move $s1, $t5                # Store the actual length in $s1


    # Initialize variables for processing
    la   $t0, input_buffer       # Load address of input buffer
    li   $t5, 0                   # Initialize bit index for storing
    li   $t8, 0                   # Initialize halfword accumulator

    # Point $t0 to the last character of the string
    add $t0, $t0, $s1            # $t0 now points to the end of the string
    addi $t0, $t0, -1              # $t0 now points to the last character

process_string:
    lb   $t3, 0($t0)             # Load the current character
    beq  $t3, 10, store_halfword      # If it's a newline (ASCII 10), store the value
    beq  $t3, 0, store_halfword       # If it's null terminator, store the value
    beq  $t3, '0', next_bit       # If it's '0', skip storing
    beq  $t3, '1', store_one      # If it's '1', store it as 1

next_bit:
    addi $t0, $t0, -1              # Move to the next character
    addi $t5, $t5, 1              # Increment the bit index
    sll  $t8, $t8, 1              # Shift left to make space for a new bit
    bne  $t5, 15, process_string   # If less than 16 bits, continue
    
    
    
    j store_halfword                 # Jump to storing halfword label

store_one:
    # Shift the current value left by 1 to make space for the new bit
    sll  $t8, $t8, 1              # Shift left to make space for a new bit
    li   $t4, 1                   # Load value 1 to store
    or   $t8, $t8, $t4            # Set the least significant bit to 1
    addi $t0, $t0, -1              # Move to the next character
    addi $t5, $t5, 1              # Increment the bit index
    bne  $t5, 15, process_string   # If less than 16 bits, continue


store_halfword:
    # Store the current haldword and reset
    sh   $t8, 0($s2)       # Store the resulting halfword in memory
    addi $s2, $s2, 2             # Increment pointer to next halfword 


    li   $t8, 0                   # Clear accumulator for next halfword
    li   $t5, 0                   # Reset bit index
    addi $t9, $t9, -1             # Decrement number of halfwords we have per number
  
    bne $t9, 0, process_string  # If we used all halfwords per number ask for next number
    

check_input_loop:
    #clear buffer
    la   $t0, input_buffer    # Load the address of the input buffer into $t0
    move  $t5, $s1              # Load the number of bytes to clear (e.g., $s0 bytes)
clear_buffer:
    sb   $zero, 0($t0)        # Store zero in the current byte pointed to by $t0
    addi $t0, $t0, 1           # Move to the next byte in the buffer
    addi $t5, $t5, -1          # Decrement the byte count
    bne  $t5, $zero, clear_buffer  # Repeat until all bytes are cleared

    # Increment loop counter and check if more numbers need to be input
    addi $t7, $t7, 1
    bne $t7, $t1, input_loop     # If counter != n, continue the input loop





# Find all combinations	----------------------------------------------------------------------------------------------------
  addu $t0, $t2, $t2  # step - $t0 (number of bytes in one user number)	
  move $t2, $t0		# $t2 - offset between the first and the second term of Hamming distance	
  move $t1, $zero	# $t1- offset between the begining of the array and the first term of Hamming distance
  # $t6 - len array-
  

  Loop:
  move $t7, $zero         # Initialize counter to 0
  move $t8, $zero	# offset for half words inside of one user's number

  halfWLoop:
  addu $t4, $t1, $s0	# calculate the position of the first term of Hamming distance (s0 - is the beginning of an array)
  addu $t4, $t4, $t8	# t8 - offset for another part (halfword) of user's number
  lh $t4, 0($t4)  	# Load 2 bytes from the given position in the array 
  
move $t3, $t6	# Since our "imm" value is only 5 bits, we cannot jump further than 15 instruction up, 
Loop_0:							# so we had to break the bigest jump into 3 smaller ones 
bne $t3, $t6, Loop										# to meet this condition					
  
  addu $t3, $t1, $t2	
  addu $t5, $t3, $s0	# calculate the position of the second term of Hamming distance
  addu $t5, $t5, $t8	# t8 - offset for another part (halfword) of user's number
  lh $t5, 0($t5)	# Load 2 bytes from the given position in the array
  
  # Getting the Hamming Distance $t4, $t5     
  xor $t4, $t4, $t5
    
# Start counting ones in the number
bit_loop:
andi $t5, $t4, 0x1       # Mask the least significant bit (LSB) and write the result into $t6
addu $t7, $t7, $t5         # if LSB ($t5) is one, then it is increased; 
        								# otherwise, nothing changes
srl $t4, $t4, 1		# shift right to proceed to the next bit
bne $t4, $zero, bit_loop    # Exit loop if $t5 becomes 0 (all non-zero bits processed)


    addiu $t8, $t8, 2	# move to the next part of the user's number
    bne $t8,$t0, halfWLoop # when the offset equals to number of bytes in one user number, we reached the end of this number
										    # and now can print the Hamming Distance
    
    
move $t3, $t6	# Since our "imm" value is only 5 bits, we cannot jump further than 15 instruction up, 
Loop_1:							# so we had to break the bigest jump into 3 smaller ones 
bne $t3, $t6, Loop_0										# to meet this condition
 

    move $a0, $t7                 # Move the count of ones into $a0 for printing
    addi $v0, $zero, 1                     # Syscall for print integer
    syscall                        # Print the Hamming Distance

#Print the separator	
    addi $v0, $zero, 11                     # Syscall for print char
    addi $a0, $zero, 9              # Load the ASCII value of 'tab' (9 in decimal) into $a0
    syscall                       # Print the separator

  
  addu $t2, $t2, $t0		# increment the offset ($t2) by step ($t0)
  addu $t3, $t1, $t2
  bne $t3, $t6, Loop_1		# if position of the second term reached the end of the array, move to the next combination
  
  move $t2, $t0			# Reset $t2 
  addu $t1, $t1, $t0		# increment the offset ($t1) by step ($t0)
  addu $t3, $t1, $t2
  bne $t3, $t6, Loop_1		# if position of the first term reached one halfword before the end of the array,
  										# then all combinations are calculated
  										
  addi $v0,$zero, 10                # Syscall to exit
  syscall
