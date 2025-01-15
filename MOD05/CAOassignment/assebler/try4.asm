.data
separator: .asciiz ", "   # Store the separator string with null termination
sep_addr: .word separator  # Store the address of the separator string
prompt: .asciiz "Input number: " # Store the prompt string
prompt1: .asciiz "Word in decimal: " # Store the prompt string
prompt2: .asciiz "Amount of words per each: " # Store the prompt string
prompt3: .asciiz "Array length in bytes: " # Store the prompt string
prompt4: .asciiz "Word added to array: " # Store the prompt string
prompt5: .asciiz "Length of the input: " # Store the prompt string
ask_seq: .asciiz "How many numbers u want to input? " # Store the prompt string
ask_len: .asciiz "What size (in bits) are your values? " # Store the prompt string
newline: .asciiz "\n"    # Define a string with just a newline character
input_buffer: .space 256        # Buffer for input (adjust size as needed)


#seq_: .word 2    # sequence of numbers
#len_: .word 34

.text
.globl main

main:

    # Print the prompt
    li $v0, 4                    # Syscall for print string
    la $a0, ask_seq               # Load address of prompt
    syscall                      # Print the prompt

     # Read integer input from user
    li $v0, 5                    # Syscall for read integer
    syscall                       # Execute the syscall
    move $t1, $v0                # Store the input integer from $v0 into $t0 (or use it directly)

    # Print the prompt
    li $v0, 4                    # Syscall for print string
    la $a0, ask_len               # Load address of prompt
    syscall                      # Print the prompt

     # Read integer input from user
    li $v0, 5                    # Syscall for read integer
    syscall                       # Execute the syscall
    move $t2, $v0                # Store the input integer from $v0 into $t0 (or use it directly)

    
   


    # Assume $t2 holds the value of b
    move $t3, $t2            # Copy original value of len_ to $t3 for later use
    srl $t2, $t2, 5          # Divide the len_ of one sequence by 32 bits
    andi $t4, $t3, 0x1F       # Get the remainder of the original value b divided by 32 (only keep the last 5 bits)
    bnez $t4, round_up       # If remainder is not zero, branch to round_up


# Continue here if no rounding is needed
j allocate_memory

round_up:
    addi $t2, $t2, 1               # Increment $t2 to round up




allocate_memory:
    move $t5, $zero                # Initialize $t5 to 0 (total number of words to allocate)
    move $t3, $t1                  # Move seq_ to $t3 for the loop counter

add_words:
    add $t5, $t5, $t2              # $t5 += $t2 (number of halfwords per element)
    addi $t3, $t3, -1             # Decrement the counter ($t3) by 1
    bne $t3, $zero, add_words  # If $t3 (counter) != 0, go to add_halfwords

    # Since each word is 4 bytes, multiply the number of words by 4 for total bytes
    sll $t5, $t5, 2                # $t5 = $t5 * 4 




    # Syscall to allocate memory dynamically using sbrk
    li $v0, 9                      # Syscall number for sbrk
    move $a0, $t5                  # Pass total bytes to allocate
    syscall                        # Allocate memory
    move $s0, $v0                  # Save base address of the allocated memory in $s0

    # Print the prompt
    li $v0, 4                    # Syscall for print string
    la $a0, prompt2               # Load address of prompt
    syscall                      # Print the prompt
    # Print the value of $t2
    li $v0, 1                      # Syscall for print integer
    move $a0, $t2                  # Move the value of $t2 to $a0
    syscall                        # Make the syscall to print
    li $v0, 4              # Syscall for print string
    la $a0, newline        # Load address of newline string
    syscall                # Make the syscall

      # Print the prompt
    li $v0, 4                    # Syscall for print string
    la $a0, prompt3               # Load address of prompt
    syscall                      # Print the prompt
     # Print the value of $t2
    li $v0, 1                      # Syscall for print integer
    move $a0, $t1                  # Move the value of $t2 to $a0
    syscall                        # Make the syscall to print
    li $v0, 4              # Syscall for print string
    la $a0, newline        # Load address of newline string
    syscall                # Make the syscall

    # Input loop to get seq_ numbers from the user and store them in the array
    move $t6, $s0         # $t6 will be the pointer to the current array element
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

    # Print the prompt
    li $v0, 4                    # Syscall for print string
    la $a0, prompt5               # Load address of prompt
    syscall                      # Print the prompt
     # Print the value of $t2
    li $v0, 1                      # Syscall for print integer
    move $a0, $s1                  # Move the value of $t2 to $a0
    syscall                        # Make the syscall to print
    li $v0, 4              # Syscall for print string
    la $a0, newline        # Load address of newline string
    syscall                # Make the syscall


    # Initialize variables for processing
    la   $t0, input_buffer       # Load address of input buffer
    li   $t5, 0                   # Initialize bit index for storing
    li   $t8, 0                   # Initialize word accumulator

    # Point $t0 to the last character of the string
    add $t0, $t0, $s1            # $t0 now points to the end of the string
    addi $t0, $t0, -1              # $t0 now points to the last character

process_string:
    lb   $t3, 0($t0)             # Load the current character
    beq  $t3, 10, store_word      # If it's a newline (ASCII 10), store the value
    beq  $t3, 0, store_word       # If it's null terminator, store the value
    beq  $t3, '0', next_bit       # If it's '0', skip storing
    beq  $t3, '1', store_one      # If it's '1', store it as 1

next_bit:
    addi $t0, $t0, -1              # Move to the next character
    addi $t5, $t5, 1              # Increment the bit index
    sll  $t8, $t8, 1              # Shift left to make space for a new bit
    bne  $t5, 32, process_string   # If less than 32 bits, continue
    j store_word                 # Jump to storing word label

store_one:
    # Shift the current value left by 1 to make space for the new bit
    sll  $t8, $t8, 1              # Shift left to make space for a new bit
    li   $t4, 1                   # Load value 1 to store
    or   $t8, $t8, $t4            # Set the least significant bit to 1
    addi $t0, $t0, -1              # Move to the next character
    addi $t5, $t5, 1              # Increment the bit index
    bne  $t5, 32, process_string   # If less than 32 bits, continue

store_word:
    # Store the current word and reset
    sw   $t8, 0($t6)       # Store the resulting word in memory
    addi $t6, $t6, 4             # Increment pointer to next word 


     # Print the prompt
    li $v0, 4                    # Syscall for print string
    la $a0, prompt4               # Load address of prompt
    syscall                      # Print the prompt
    # Print the value of $t2
    li $v0, 1                      # Syscall for print integer
    move $a0, $t8                  # Move the value of $t2 to $a0
    syscall                        # Make the syscall to print
    li $v0, 4              # Syscall for print string
    la $a0, newline        # Load address of newline string
    syscall                # Make the syscall


    li   $t8, 0                   # Clear accumulator for next word
    li   $t5, 0                   # Reset bit index
    addi $t9, $t9, -1             # Decrement number of words we have per number
  
    bne $t9, 0, process_string  # If we used all words per number ask for next number
                 # Continue processing the next bits

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

    # Print the stored words as decimals
    move $t6, $s0                  # Reset pointer to the beginning of the allocated memory
    mul $t3, $t1, $t2      # Multiply $t1 by $t2 and store the result in $t3
print_loop:
    
    # Print the prompt
    li $v0, 4                    # Syscall for print string
    la $a0, prompt1               # Load address of prompt
    syscall                      # Print the prompt

    lw $t8, 0($t6)                 # Load the word from memory
    li $v0, 1                       # Syscall for print integer
    move $a0, $t8                  # Move the word to $a0 for printing
    syscall                        # Print the word

    li $v0, 4              # Syscall for print string
    la $a0, newline        # Load address of newline string
    syscall                # Make the syscall

    addi $t6, $t6, 4                # Move to the next word
    addi $t3, $t3, -1               # Decrement the loop counter
    bne $t3, $zero, print_loop      # If counter not zero, continue printing


  addi $v0,$zero, 10                # Syscall to exit
  syscall
