/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */


package com.io7m.genevan.tests;

import com.io7m.genevan.core.GenProtocolVersion;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static java.math.BigInteger.ZERO;
import static java.math.BigInteger.valueOf;

/**
 * Tests for protocol versions.
 */

public final class GenProtocolVersionTest
{
  /**
   * Negative major versions are not allowed.
   */

  @Test
  public void testNegativeMajor()
  {
    Assertions.assertThrows(IllegalArgumentException.class, () -> {
      new GenProtocolVersion(valueOf(-1), ZERO);
    });
  }

  /**
   * Negative minor versions are not allowed.
   */

  @Test
  public void testNegativeMinor()
  {
    Assertions.assertThrows(IllegalArgumentException.class, () -> {
      new GenProtocolVersion(ZERO, valueOf(-1));
    });
  }
}
