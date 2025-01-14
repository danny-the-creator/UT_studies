import random
import time

def get_av_waiting_time(n_cmp, prob, n_pk):

    queue = []
    total_waiting_time = 0
    count = 0

    while count < n_pk:

        for j in range(n_cmp):

            randomint = random.randint(1, 100)

            if randomint <= prob * 100:

                queue.append(["packet", len(queue)])
                count += 1

        if len(queue) > 0:
            total_waiting_time += queue[0][1]
            queue.pop(0)

    av_waiting_time = total_waiting_time / n_pk
    return av_waiting_time


# runs the function 100 times for a given input
# returns the min, max and avg of the results

def numbers_get_av_waiting_time(n_cmp, prob, n_pk):

    start = time.time()

    results = []
    string_inputs = "Number of computers = " + str(n_cmp) + " , probability = " + str(prob) + " number of packets = " + str(n_pk)
    # return get_av_waiting_time(n_cmp, prob, n_pk)
    for i in range(1):
        av_waiting_time = get_av_waiting_time(n_cmp, prob, n_pk)
        results.append(av_waiting_time)

    min_val = min(results)
    max_val = max(results)
    avg_val = sum(results) / 2              # Assuming 50 is the total count of results

    end = time.time()

    result_string = (
            string_inputs + "\n"
            + "Waiting times:" + "\n"
            + "Min: " + str(min_val) + "\n"
            + "Max: " + str(max_val) + "\n"
            + "Average: " + str(avg_val) + "\n"
            + "Total time: " + str(end-start) + " seconds"
    )

    return result_string

print(numbers_get_av_waiting_time(20, 0.1, 100000))