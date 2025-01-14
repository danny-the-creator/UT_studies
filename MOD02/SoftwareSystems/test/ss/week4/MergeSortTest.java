package ss.week4;

import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;


public class MergeSortTest {
    @Test
    public void testMergesortEmptyList() {
        List<Integer> sequence = new ArrayList<>(Collections.emptyList());
        List<Integer> result = MergeSort.mergeSort(sequence);
        assertEquals(Collections.emptyList(), result);
    }

    @Test
    public void testMergesortSingleItem() {
        List<Integer> sequence = new ArrayList<>(Arrays.asList(1));
        List<Integer> result = MergeSort.mergeSort(sequence);
        assertEquals(Arrays.asList(1), result);
    }

    @Test
    public void testMergesortSortedList() {
        List<Integer> sequence = new ArrayList<>(Arrays.asList(1, 2, 3, 4, 5));
        List<Integer> result = MergeSort.mergeSort(sequence);
        assertEquals(Arrays.asList(1, 2, 3, 4, 5), result);

        sequence = new ArrayList<>(Arrays.asList(1, 2, 3, 4, 5, 6));
        result = MergeSort.mergeSort(sequence);
        assertEquals(Arrays.asList(1, 2, 3, 4, 5, 6), result);
    }

    @Test
    public void testMergesortUnsortedList() {
        List<Integer> sequence = new ArrayList<>(Arrays.asList(3, 2, 1, 5, 4));
        List<Integer> result = MergeSort.mergeSort(sequence);
        assertEquals(Arrays.asList(1, 2, 3, 4, 5), result);

        sequence = new ArrayList<>(Arrays.asList(3, 2, 1, 6, 5, 4));
        result = MergeSort.mergeSort(sequence);
        assertEquals(Arrays.asList(1, 2, 3, 4, 5, 6), result);
    }
    @Test
    public void testOriginal() {
        List<Integer> seq = new ArrayList<>(20000);

        IntStream.range(0, 20000).mapToObj(i -> (int) (Math.random() * 1000)).forEach(seq::add);
        List<Integer> seq2 = new ArrayList<>(seq);
        Collections.sort(seq);
        assertEquals(seq, MergeSort.mergeSort(seq2));
    }
}