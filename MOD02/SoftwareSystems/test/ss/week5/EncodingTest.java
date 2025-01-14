package ss.week5;

import org.apache.commons.codec.DecoderException;
import org.apache.commons.codec.binary.Base64;
import org.apache.commons.codec.binary.BinaryCodec;
import org.apache.commons.codec.binary.Hex;
import org.apache.commons.codec.binary.StringUtils;

/**
 * A simple class that experiments with the Hex encoding
 * of the Apache Commons Codec library.
 *
 */
public class EncodingTest {
    public static void main(String[] args) throws DecoderException {
        String input = "Hello Big World";
        byte[] hex_input = Hex.decodeHex("4d6f64756c652032".toCharArray());
        String result = StringUtils.newStringUtf8(hex_input);
        System.out.println(Hex.encodeHexString(input.getBytes()));
        System.out.println(result);

        // Base 64
        byte[] word = "Hello␣World".getBytes();
        byte[] data = Hex.decodeHex("010203040506".toCharArray());
        result = Base64.encodeBase64String(data);
        System.out.println(result);
        data = Base64.decodeBase64("U29mdHdhcmUgU3lzdGVtcw==");
        result = StringUtils.newStringUtf8(data);
        System.out.println(result);

        System.out.println(Base64.encodeBase64String("a".getBytes()));
        System.out.println(Base64.encodeBase64String("aa".getBytes()));
        System.out.println(Base64.encodeBase64String("aaa".getBytes()));
        System.out.println(Base64.encodeBase64String("aaaa".getBytes()));
        System.out.println(Base64.encodeBase64String("aaaaa".getBytes()));
        System.out.println(Base64.encodeBase64String("aaaaaaaaaa".getBytes()));
    }
}
